(define always-wrap-reified? (make-parameter #f))

; Scope object.
; Used to determine whether a branch has occured between variable
; creation and unification to allow the set-var-val! optimization
; in subst-add. Both variables and substitutions will contain a
; scope. When a substitution flows through a conde it is assigned
; a new scope.

; Creates a new scope that is not scope-eq? to any other scope
(define (new-scope) (list 'scope))
(define scope-eq? eq?)

; Scope used when variable bindings should always be made in the
; substitution, as in disequality solving and reification. We
; don't want to set-var-val! a variable when checking if a
; disequality constraint holds!
(define nonlocal-scope (list 'non-local-scope))


; Logic variable object.
; Contains:
;   val - value for variable assigned by unification using
;      set-var-val! optimization. unbound if not yet set or
;      stored in substitution.
;   scope - scope that the variable was created in.
;   idx - unique numeric index for the variable. Used by the
;      trie substitution representation.
; Variable objects are compared by object identity.

; The unique val for variables that have not yet been bound
; to a value or are bound in the substitution. Also used
; as the sentinal value for substitution and constraint store
; lookup.
(define unbound (list 'unbound))
(define (unbound? v) (eq? v unbound))

(define var
  (let ((counter -1))
    (lambda (scope)
      (set! counter (+ 1 counter))
      (vector unbound scope counter))))

; Vectors are not allowed as terms, so terms that are vectors
; are variables.
(define (var? x) (vector? x))

(define var-eq? eq?)

(define (var-val x)   (vector-ref x 0))
(define (var-scope x) (vector-ref x 1))
(define (var-idx x)   (vector-ref x 2))

(define (set-var-val! x v)
  (vector-set! x 0 v))


; Substitution object.
; Contains:
;   map - mapping of variables to values
;   scope - scope at current program point, for set-var-val!
;     optimization. Updated at conde. Included in the substitution
;     because it is required to fully define the substitution
;     and how it is to be extended.
;
; Implementation of the substitution map depends on the Scheme used,
; as we need a map. See mk.rkt and mk-vicare.scm.

(define empty-subst-map empty-intmap)
(define subst-map-length intmap-count)
(define (subst-map-lookup u S)
  (intmap-ref S (var-idx u)))
(define (subst-map-add S var val)
  (intmap-set S (var-idx var) val))

(define (subst mapping scope)
  (cons mapping scope))

(define subst-map car)
(define subst-scope cdr)

(define (subst-length S)
  (subst-map-length (subst-map S)))

(define (subst-with-scope S new-scope)
  (subst (subst-map S) new-scope))

(define empty-subst (subst empty-subst-map (new-scope)))

(define (subst-add S x v)
  ; set-var-val! optimization: set the value directly on the
  ; variable object if we haven't branched since its creation
  ; (the scope of the variable and the substitution are the same).
  ; Otherwise extend the substitution mapping.
  (if (scope-eq? (var-scope x) (subst-scope S))
    (begin (set-var-val! x v)
           S)
    (subst (subst-map-add (subst-map S) x v) (subst-scope S))))

(define (subst-lookup x S)
  ; set-var-val! optimization.
  ; Tried checking the scope here to avoid a subst-map-lookup
  ; if it was definitely unbound, but that was slower.
  (if (not (unbound? (var-val x)))
    (var-val x)
    (subst-map-lookup x (subst-map S))))

; Association object.
; Describes an association mapping the lhs to the rhs. Returned by
; unification to describe the associations that were added to the
; substitution (whose representation is opaque) and used to represent
; disequality constraints.
(define lhs car)
(define rhs cdr)

; Constraint record object.
;
; Describes the constraints attached to a single variable.
;
; Contains:
;   T - type constraint. instance of type-constraint or #f to indicate
;         no constraint
;   D - list of disequality constraints. Each disequality is a list of
;         associations. The constraint is violated if all associated
;         variables are equal in the substitution simultaneously. D
;         could contain duplicate constraints (created by distinct =/=
;         calls). A given disequality constraint is only attached to
;         one of the variables involved, as all components of the
;         constraint must be violated to cause failure.
;   A - list of absento constraints. Each constraint is a term.
;         The list contains no duplicates.

(define empty-c '(#f () ()))

(define (c-T c) (car c))
(define (c-D c) (cadr c))
(define (c-A c) (caddr c))

(define (c-with-T c T) (list T (c-D c) (c-A c)))
(define (c-with-D c D) (list (c-T c) D (c-A c)))
(define (c-with-A c A) (list (c-T c) (c-D c) A))

; Constraint store object.
; Mapping of representative variable to constraint record. Constraints
; are always on the representative element and must be moved / merged
; when that element changes.

(define empty-C empty-intmap)

(define (set-c st x c)
  (state-with-C
    st
    (intmap-set (state-C st) (var-idx x) c)))

(define (lookup-c st x)
  (let ((res (intmap-ref (state-C st) (var-idx x))))
    (if (unbound? res)
      empty-c
      res)))

; t:unbind in mk-vicare.scm either is buggy or doesn't do what I would expect, so
; I implement remove by setting the value to the empty constraint record.
(define (remove-c x st)
  (state-with-C st (intmap-set (state-C st) (var-idx x) empty-c)))


; State object.
; The state is the value that is monadically passed through the search
; Contains:
;   S - the substitution
;   C - the constraint store

(define (state S C) (cons S C))

(define (state-S st) (car st))
(define (state-C st) (cdr st))

(define empty-state (state empty-subst empty-C))

(define (state-with-C st C^)
  (state (state-S st) C^))

(define state-with-scope
  (lambda (st new-scope)
    (state (subst-with-scope (state-S st) new-scope) (state-C st))))

; Unification

; UnificationResult: (or/c (values Substitution (Listof Association))
;                          (values #f #f)
; An extended substitution and a list of associations added during the unification,
;  or (values #f #f) indicating unification failed.

; Term, Term, Substitution -> UnificationResult
(define (unify u v s)
  (let ((u (walk u s))
        (v (walk v s)))
    (cond
      ((eq? u v) (values s '()))
      ((and (var? u) (var? v))
       (if (> (var-idx u) (var-idx v))
         (ext-s-check u v s)
         (ext-s-check v u s)))
      ((var? u) (ext-s-check u v s))
      ((var? v) (ext-s-check v u s))
      ((and (pair? u) (pair? v))
       (let-values (((s added-car) (unify (car u) (car v) s)))
         (if s
           (let-values (((s added-cdr) (unify (cdr u) (cdr v) s)))
             ; Right now appends the list of added values from sub-unifications.
             ; Alternatively could be threaded monadically, which could be faster
             ; or slower.
             (values s (append added-car added-cdr)))
           (values #f #f))))
      ((equal? u v) (values s '()))
      (else (values #f #f)))))

; Term, Substitution -> Term
(define (walk u S)
  (let rec ((u u))
    (if (var? u)
      (let ((val (subst-lookup u S)))
        (if (unbound? val)
          u
          (rec val)))
      u)))

; Var, Term, Substitution -> Boolean
(define (occurs-check x v S)
  (let ((v (walk v S)))
    (cond
      ((var? v) (var-eq? v x))
      ((pair? v)
       (or (occurs-check x (car v) S)
           (occurs-check x (cdr v) S)))
      (else #f))))

; Var, Term, Substitution -> UnificationResult
(define (ext-s-check x v S)
  (if (occurs-check x v S)
    (values #f #f)
    (values (subst-add S x v) (list (cons x v)))))

(define (unify* S+ S)
  (unify (map lhs S+) (map rhs S+) S))

; Search

; SearchStream: #f | SuspendedStream | State | (Pair State SuspendedStream)
; SuspendedStream: (-> SearchStream)

; Match on search streams. The State type must not be a pair with a procedure
; in its cdr, lest a single result be interpreted as multiple results.
;
; (() e0)     failure
; ((f) e1)    suspension for interleaving. separate from success or failure to ensure
;              it goes all the way to the top of the tree.
; ((c) e2)    single result. Used rather than (cons c (lambda () #f))
;              to avoid returning to search a part of the tree that
;              will inevitably fail.
; ((c f) e3)  multiple results. `f` is a thunk to avoid unnecessary computation
;              in the case that the LHS the last answer needed to satisfy the
;              query. It also triggers interleaving; the search looks for
;              answers in alternate branches before returning.
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((stream e))
       (cond
         ((not stream) e0)
         ((procedure? stream)  (let ((f^ stream)) e1))
         ((not (and (pair? stream)
                 (procedure? (cdr stream))))
          (let ((c^ stream)) e2))
         (else (let ((c (car stream)) (f (cdr stream)))
                 e3)))))))

; SearchStream, SuspendedStream -> SearchStream,
;
; f is a thunk to avoid unnecesarry computation in the case that the
; first answer produced by c-inf is enough to satisfy the query.
(define (mplus stream f)
  (case-inf stream
    (() (f))
    ((f^) (lambda () (mplus (f) f^)))
    ((c) (cons c f))
    ((c f^) (cons c (lambda () (mplus (f) f^))))))

; SearchStream, Goal -> SearchStream
(define (bind stream g)
  (case-inf stream
    (() #f)
    ((f) (lambda () (bind (f) g)))
    ((c) (g c))
    ((c f) (mplus (g c) (lambda () (bind (f) g))))))

; Int, SuspendedStream -> (ListOf SearchResult)
(define (take n f)
  (if (and n (zero? n))
    '()
    (case-inf (f)
      (() '())
      ((f) (take n f))
      ((c) (cons c '()))
      ((c f) (cons c (take (and n (- n 1)) f))))))

; (bind* e:SearchStream g:Goal ...) -> SearchStream
(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

; (suspend e:SearchStream) -> SuspendedStream
; Used to clearly mark the locations where search is suspended in order to
; interleave with other branches.
(define-syntax suspend (syntax-rules () ((_ body) (lambda () body))))

; (mplus* e:SearchStream ...+) -> SearchStream
(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...)
     (mplus e0 (suspend (mplus* e ...))))))

; (fresh (x:id ...) g:Goal ...+) -> Goal
(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambda (st)
       (suspend
         (let ((scope (subst-scope (state-S st))))
           (let ((x (var scope)) ...)
             (bind* (g0 st) g ...))))))))

; (conde [g:Goal ...] ...+) -> Goal
(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambda (st)
       (suspend
         (let ((st (state-with-scope st (new-scope))))
           (mplus*
             (bind* (g0 st) g ...)
             (bind* (g1 st) g^ ...) ...)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (take n
           (suspend
             ((fresh (q) g0 g ...
                     (lambda (st)
                       (let ((st (state-with-scope st nonlocal-scope)))
                         (let ((z ((reify q) st)))
                           (cons z (lambda () (lambda () #f)))))))
              empty-state))))
    ((_ n (q0 q1 q ...) g0 g ...)
     (run n (x)
       (fresh (q0 q1 q ...)
         g0 g ...
         (== (list q0 q1 q ...) x))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (q0 q ...) g0 g ...) (run #f (q0 q ...) g0 g ...))))


(define-syntax defrel
  (syntax-rules ()
   ;; No suspend given single goal; search order for relations designed with define
   ((_ (name arg ...) g)
    (define (name arg ...) g))
   ;; Use of fresh suspends when forming a conjunction to avoid nontermination
   ((_ (name arg ...) g ...)
    (define (name arg ...) (fresh () g ...)))))



; Constraints
; C refers to the constraint store map
; c refers to an individual constraint record

; Constraint: State -> (or/c #f State)
;
; (note that a Constraint is a Goal but a Goal is not a Constraint.
;  Constraint implementations currently use this more restrained type.
;  See `and-foldl` and `update-constraints`.)

; Invariants assumed for type constraints:
; 1. Must be positive, not negative. not-pairo wouldn't work.
; 2. Each type must have infinitely many possible values to avoid
;      incorrectness in combination with disequality constraints,
;      like: (fresh (x) (booleano x) (=/= x #t) (=/= x #f))
; 3. Types must be disjoint from each other and from pairs.

; Predicate: Any -> (or #f Any)
; CompareResult: (or '< '> '=)
; Ordering: T, T -> CompareResult where T is defined by the corresponding predicate.

; Predicate Symbol CompareResult -> TypeConstraint
(define (type-constraint predicate reified ordering)
  (list predicate reified ordering))

(define type-constraint-predicate car)
(define type-constraint-reified cadr)
(define type-constraint-ordering caddr)

; TypeConstraint -> (Term -> Goal)
(define (apply-type-constraint tc)
  (lambda (u)
    (lambda (st)
      (let ((type-pred (type-constraint-predicate tc)))
        (let ((term (walk u (state-S st))))
          (cond
            ((type-pred term) st)
            ((var? term)
             (let* ((c (lookup-c st term))
                    (T (c-T c)))
               (cond
                 ((eq? T tc) st)
                 ((not T) (set-c st term (c-with-T c tc)))
                 (else #f))))
            (else #f)))))))

(define-syntax declare-type-constraints
  (syntax-rules ()
    ((_ tc-list (name predicate reified ordering) ...)
     (begin
       (define tc-list (list (type-constraint predicate 'reified ordering) ...))
       (define-values
         (name ...)
         (apply values (map apply-type-constraint tc-list)))))))

; Orderings
(define (number-compare a b) (cond ((= a b) '=) ((< a b) '<) (else '>)))
(define (string-compare a b) (cond ((string=? a b) '=) ((string<? a b) '<) (else '>)))
(define (symbol-compare a b) (string-compare (symbol->string a) (symbol->string b)))

(declare-type-constraints type-constraints
  (numbero number? num number-compare)
  (stringo string? str string-compare)
  (symbolo symbol? sym symbol-compare))

(define (add-to-D st v d)
  (let* ((c (lookup-c st v))
         (c^ (c-with-D c (cons d (c-D c)))))
    (set-c st v c^)))

; (ListOf Association) -> Goal
(define (=/=* S+)
  (lambda (st)
    (let-values (((S added) (unify* S+ (subst-with-scope
                                         (state-S st)
                                         nonlocal-scope))))
      (cond
        ((not S) st)
        ((null? added) #f)
        (else
          ; Attach the constraint to variables in of the disequality elements
          ; (el).  We only need to choose one because all elements must fail to
          ; cause the constraint to fail.
          (let ((el (car added)))
            (let ((st (add-to-D st (car el) added)))
              (if (var? (cdr el))
                (add-to-D st (cdr el) added)
                st))))))))

; Term, Term -> Goal
(define (=/= u v)
  (=/=* (list (cons u v))))

; Term, Term -> Goal
; Generalized 'absento': 'term1' can be any legal term (old version
; of faster-miniKanren required 'term1' to be a ground atom).
(define (absento term1 term2)
  (lambda (st)
    (let ((term1 (walk term1 (state-S st)))
          (term2 (walk term2 (state-S st))))
      (let ((st^ ((=/= term1 term2) st)))
        (and st^
             (cond
               ((pair? term2)
                (let ((st^^ ((absento term1 (car term2)) st^)))
                  (and st^^ ((absento term1 (cdr term2)) st^^))))
               ((var? term2)
                (let* ((c (lookup-c st^ term2))
                       (A (c-A c)))
                  (if (memv term1 A)
                    st^
                    (let ((c^ (c-with-A c (cons term1 A))))
                      (set-c st^ term2 c^)))))
               (else st^)))))))

; Fold lst with proc and initial value init. If proc ever returns #f,
; return with #f immediately. Used for applying a series of
; constraints to a state, failing if any operation fails.
(define (and-foldl proc init lst)
  (if (null? lst)
    init
    (let ((res (proc (car lst) init)))
      (and res (and-foldl proc res (cdr lst))))))

(define (== u v)
  (lambda (st)
    (let-values (((S^ added) (unify u v (state-S st))))
      (if S^
        (and-foldl update-constraints (state S^ (state-C st)) added)
        #f))))

; Not fully optimized. Could do absento update with fewer
; hash-refs / hash-sets.
(define (update-constraints a st)
  (let ((old-c (lookup-c st (lhs a))))
    (if (eq? old-c empty-c)
      st
      (let ((st (remove-c (lhs a) st)))
       (and-foldl (lambda (op st) (op st)) st
        (append
          (if (c-T old-c)
            (list ((apply-type-constraint (c-T old-c)) (rhs a)))
            '())
          (map (lambda (atom) (absento atom (rhs a))) (c-A old-c))
          (map =/=* (c-D old-c))))))))

(define (walk* v S)
  (let ((v (walk v S)))
    (cond
      ((var? v) v)
      ((pair? v)
       (cons (walk* (car v) S) (walk* (cdr v) S)))
      (else v))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g g* ...)
     (lambda (st)
       (let ((x (walk* x (state-S st))) ...)
         ((fresh () g g* ...) st))))))

(define succeed (== #f #f))
(define fail (== #f #t))


; Reification

; S - substitution
; T - type constraints
; A - absento constriants
; D - disequality constraints

(define (reify x)
  (lambda (st)
    (let* ((S (state-S st))
           (v (walk* x S))
           (R (reify-S v (subst empty-subst-map nonlocal-scope)))
           (relevant-vars (vars v)))
      (let*-values (((T D A) (extract-and-normalize st relevant-vars x))
                    ((D A)   (drop-irrelevant D A relevant-vars))
                    ((D A)   (drop-subsumed D A st)))
        (form (walk* v R)
              (walk* D R)
              (walk* T R)
              (walk* A R))))))

(define (vars term)
  (let rec ((term term) (acc '()))
    (cond
      ((var? term) (cons term acc))
      ((pair? term)
       (rec (cdr term) (rec (car term) acc)))
      (else (remove-duplicates acc)))))

(define (extract-and-normalize st relevant-vars x)
  (define T (map (lambda (tc-type)
                   (cons (type-constraint-reified tc-type)
                         (filter-map (lambda (x)
                                       (let ((tc (c-T (lookup-c st x))))
                                         (and (eq? tc tc-type)
                                              x)))
                                     relevant-vars)))
                 type-constraints))
  (define D (append*
              (map (lambda (x)
                     (filter-map (normalize-diseq (state-S st)) (c-D (lookup-c st x))))
                   relevant-vars)))
  (define A (append*
              (map (lambda (x)
                     (map (lambda (a-lhs)
                            (cons (walk* a-lhs (state-S st))
                                  x))
                          (c-A (lookup-c st x))))
                   relevant-vars)))

  (values T D A))

(define (normalize-diseq S)
  (lambda (S+)
    (let-values (((S^ S+^) (unify* S+ S)))
      (and S^ (walk* S+^ S)))))

; Drop constraints that are satisfiable in any assignment of the reified
; variables, because they refer to unassigned variables that are not part of
; the answer, which can be assigned as needed to satisfy the constraint.
(define (drop-irrelevant D A relevant-vars)
  (define (all-relevant? t)
    (andmap (lambda (v) (member v relevant-vars))
            (vars t)))
  (values (filter all-relevant? D)
          (filter all-relevant? A)))


(define (drop-subsumed D A st)
  (define D^ (rem-subsumed
                 d-subsumed-by?
                 (filter (lambda (d)
                           (not (or (d-subsumed-by-T? d st)
                                    (d-subsumed-by-A? d A st))))
                         D)))
  (define A^ (rem-subsumed
                 a-subsumed-by?
                 (filter (lambda (a)
                           (not (or (absento-rhs-atomic? a st)
                                    (absento-rhs-occurs-lhs? a st))))
                         A)))
  (values D^ A^))

; Drop absento constraints where the RHS is known to be atomic, such that
; the disequality attached by absento solving is sufficient.
(define (absento-rhs-atomic? a st)
  ; absento on pairs is pushed down and type constraints are atomic,
  ; so the only kind of non-atomic RHS is an untyped var.
  (not (and (var? (rhs a)) (unbound? (var-type (rhs a) st)))))

; Drop absento constraints that are trivially satisfied because
; any violation would cause a failure of the occurs check.
; Example:
;  (absento (list x y z) x) is trivially true because a violation would
;  require x to occur within itself.
(define (absento-rhs-occurs-lhs? a st)
  (occurs-check (rhs a) (lhs a) (state-S st)))

; Drop disequalities that are subsumed by an absento contraint
; that is not itself equivalent to just a disequality.
(define (d-subsumed-by-A? d A st)
  (exists (lambda (a)
            (and (not (absento-rhs-atomic? a st))
                 (d-subsumed-by? d (absento->diseq a))))
          A))

; Drop disequalities that are fully satisfied because the types are disjoint
; either due to type constraints or ground values.
; Examples:
;  * given (symbolo x) and (numbero y), (=/= x y) is dropped.
(define (d-subsumed-by-T? d st)
  (exists (lambda (pr) (not (var-types-match? (lhs pr) (rhs pr) st)))
          d))

(define (var-types-match? t1 t2 st)
  (or (unbound? (var-type t1 st))
      (if (var? t2)
        (or (unbound? (var-type t2 st))
            (eq? (var-type t1 st) (var-type t2 st)))
        ((type-constraint-predicate (var-type t1 st))
         t2))))

(define (var-type x st) (or (c-T (lookup-c st x)) unbound))

(define (absento->diseq t) (list t))

(define (rem-subsumed subsumed-by? el*)
  (define (subsumed-by-one-of? el el*)
    (ormap (lambda (el2) (subsumed-by? el el2)) el*))

  (let loop ((el* el*)
             (result '()))
    (cond
      ((null? el*) result)
      (else
        (let ((el (car el*)))
          (cond
            ((or (subsumed-by-one-of? el (cdr el*))
                 (subsumed-by-one-of? el result))
             (loop (cdr el*) result))
            (else (loop (cdr el*)
                        (cons el result)))))))))

; Examples:
; * (absento `(cat . ,S) y) is subsumed by (absento S y)
;
; Note that absento constraints are pushed down to tree leaves, so we would never have
;  (absento 'closure q) given (== q (list x)). Thus we do not need to consider subsumption
;  between absento constraints on q and x.
(define (a-subsumed-by? t1 t2)
  (and (var-eq? (rhs t1) (rhs t2)) (member* (lhs t2) (lhs t1))))

(define (member* u v)
  (cond
    ((equal? u v) #t)
    ((pair? v)
     (or (member* u (car v)) (member* u (cdr v))))
    (else #f)))

; (-> disequality/c disequality/c boolean?)
; Examples:
;  * ((a . 5) (b . 6)) is subsumed by ((a . 5)) because (not (== a 5)) is a stronger constraint
;    than (not (and (== a 5) (== b 6)))
(define (d-subsumed-by? d1 d2)
  (let*-values (((S ignore) (unify* d1 (subst empty-subst-map nonlocal-scope)))
                ((S+ added) (unify* d2 S)))
               (and S+ (null? added))))

(define (reify-S v S)
  (let ((v (walk v S)))
    (cond
      ((var? v)
       (let ((n (subst-length S)))
         (let ((name (reify-name n)))
           (subst-add S v name))))
      ((pair? v)
       (let ((S (reify-S (car v) S)))
         (reify-S (cdr v) S)))
      (else S))))

; Formatting

(define (reify-name n)
  (string->symbol
    (string-append "_" "." (number->string n))))

(define (form v D T A)
  (let ((ft (filter-map
              (lambda (p)
                (let ((tc-type (car p)) (tc-vars (cdr p)))
                  (and (not (null? tc-vars))
                       `(,tc-type . ,(sort-lex tc-vars)))))
              T))
        (fd (sort-D D))
        (fa (sort-lex A)))
    (let ((fd (if (null? fd) fd
                (let ((fd (drop-dot-D fd)))
                  `((=/= . ,fd)))))
          (fa (if (null? fa) fa
                (let ((fa (drop-dot fa)))
                  `((absento . ,fa))))))
      (cond
        ((and (null? fd) (null? ft) (null? fa) (not (always-wrap-reified?)))
         v)
        (else (append `(,v) fd ft fa))))))

(define (sort-lex ls)
  (list-sort lex<=? ls))

(define (sort-D D)
  (sort-lex (map sort-d D)))

(define (sort-d d)
  (list-sort
    (lambda (x y)
      (lex<=? (car x) (car y)))
    (map sort-pr d)))

(define (symbol<? a b) (string<? (symbol->string a) (symbol->string b)))

(define (sort-pr pr)
  (let ((l (lhs pr)) (r (rhs pr)))
    (cond
      ((not (reified-var? r)) pr)
      ((symbol<? r l) `(,r . ,l))
      (else pr))))

(define (reified-var? r)
  (and (symbol? r)
       (char=? (string-ref (symbol->string r) 0)
               #\_)))

(define (drop-dot-D D)
  (map drop-dot D))

(define (drop-dot X)
  (map (lambda (t) (list (lhs t) (rhs t)))
       X))

; (Listof (Pair Predicate Ordering))
(define type-orderings
  (append
    ; atomic types
    (map (lambda (tc) (cons (type-constraint-predicate tc)
                            (type-constraint-ordering tc)))
         type-constraints)
    `(; booleans
      (,(lambda (v) (eq? v #f)) . ,(lambda (x y) '=))
      (,(lambda (v) (eq? v #t)) . ,(lambda (x y) '=))
      ; lists
      (,null? . ,(lambda (x y) '=))
      (,pair? . ,(lambda (x y)
                   (let ((r (lex-compare (car x) (car y))))
                     (if (eq? r '=)
                       (lex-compare (cdr x) (cdr y))
                       r)))))))

(define (index+element-where l pred)
  (let loop ((l l)
             (i 0))
    (cond
      [(null? l)      (values #f #f)]
      [(pred (car l)) (values i (car l))]
      [else           (loop (cdr l) (+ i 1))])))

(define (type-ordering v)
  (let-values ([(idx pr) (index+element-where type-orderings (lambda (pr) ((lhs pr) v)))])
    (if idx
      (values idx (rhs pr))
      (error 'type-index "missing ordering for type of value ~s" v))))

; (Term, Term) -> (or CompareResult error)
; defined when arguments are pairs, null, or atomic types addressed by type-constraints;
; see type-orderings.
(define (lex-compare x y)
  (let-values (((x-o-idx x-o) (type-ordering x))
               ((y-o-idx y-o) (type-ordering y)))
    (if (eqv? x-o-idx y-o-idx)
      (x-o x y)
      (number-compare x-o-idx y-o-idx))))

(define (lex<=? x y)
  (member (lex-compare x y) '(< =)))
