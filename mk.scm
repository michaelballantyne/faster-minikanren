; Scope object.
; Used to determine whether a branch has occured between variable
; creation and unification to allow the set-var-val! optimization
; in subst-add. Both variables and substitutions will contain a
; scope. When a substitution flows through a conde it is assigned
; a new scope.

; Creates a new scope that is not scope-eq? to any other scope
(define new-scope
  (lambda ()
    (list 'scope)))

; Scope used when variable bindings should always be made in the
; substitution, as in disequality solving and reification. We
; don't want to set-var-val! a variable when checking if a
; disequality constraint holds!
(define nonlocal-scope
  (list 'non-local-scope))

(define scope-eq? eq?)

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
; to a value or are bound in the substitution
(define unbound (list 'unbound))

(define var
  (let ((counter -1))
    (lambda (scope)
      (set! counter (+ 1 counter))
      (vector unbound scope counter))))

; Vectors are not allowed as terms, so terms that are vectors
; are variables.
(define var?
  (lambda (x)
    (vector? x)))

(define var-eq? eq?)

(define var-val
  (lambda (x)
    (vector-ref x 0)))

(define set-var-val!
  (lambda (x v)
    (vector-set! x 0 v)))

(define var-scope
  (lambda (x)
    (vector-ref x 1)))

(define var-idx
  (lambda (x)
    (vector-ref x 2)))


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

(define subst
  (lambda (mapping scope)
    (cons mapping scope)))

(define subst-map car)

(define subst-scope cdr)

(define subst-length
  (lambda (S)
    (subst-map-length (subst-map S))))

(define subst-with-scope
  (lambda (S new-scope)
    (subst (subst-map S) new-scope)))

(define empty-subst (subst empty-subst-map (new-scope)))

(define subst-add
  (lambda (S x v)
    ; set-var-val! optimization: set the value directly on the
    ; variable object if we haven't branched since its creation
    ; (the scope of the variable and the substitution are the same).
    ; Otherwise extend the substitution mapping.
    (if (scope-eq? (var-scope x) (subst-scope S))
      (begin
        (set-var-val! x v)
        S)
      (subst (subst-map-add (subst-map S) x v) (subst-scope S)))))

(define subst-lookup
  (lambda (u S)
    ; set-var-val! optimization.
    ; Tried checking the scope here to avoid a subst-map-lookup
    ; if it was definitely unbound, but that was slower.
    (if (not (eq? (var-val u) unbound))
      (var-val u)
      (subst-map-lookup u (subst-map S)))))

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

(define empty-c `(#f () ()))

(define c-T
  (lambda (c)
    (car c)))

(define c-D
  (lambda (c)
    (cadr c)))

(define c-A
  (lambda (c)
    (caddr c)))

(define c-with-T
  (lambda (c T)
    (list T (c-D c) (c-A c))))

(define c-with-D
  (lambda (c D)
    (list (c-T c) D (c-A c))))

(define c-with-A
  (lambda (c A)
    (list (c-T c) (c-D c) A)))

; Constraint store object.
; Mapping of representative variable to constraint record. Constraints
; are always on the representative element and must be moved / merged
; when that element changes.

(define empty-C empty-intmap)

(define (set-c st v c)
  (state-with-C
    st
    (intmap-set (state-C st) (var-idx v) c)))

(define (lookup-c st v)
  (let ((res (intmap-ref (state-C st) (var-idx v))))
    (if (not (eq? unbound res))
      res
      empty-c)))

; t:unbind in mk-chez.scm either is buggy or doesn't do what I would expect, so
; I implement remove by setting the value to the empty constraint record.
(define remove-c
  (lambda (v st)
    (state-with-C st (intmap-set (state-C st) (var-idx v) empty-c))))


; State object.
; The state is the value that is monadically passed through the search
; Contains:
;   S - the substitution
;   C - the constraint store

(define state
  (lambda (S C)
    (cons S C)))

(define state-S (lambda (st) (car st)))
(define state-C (lambda (st) (cdr st)))

(define empty-state (state empty-subst empty-C))

(define (state-with-C st C^)
  (state (state-S st) C^))

(define state-with-scope
  (lambda (st new-scope)
    (state (subst-with-scope (state-S st) new-scope) (state-C st))))

; Unification

(define walk
  (lambda (u S)
    (if (var? u)
      (let ((val (subst-lookup u S)))
        (if (eq? val unbound)
          u
          (walk val S)))
      u)))

(define occurs-check
  (lambda (x v S)
    (let ((v (walk v S)))
      (cond
        ((var? v) (var-eq? v x))
        ((pair? v)
         (or
           (occurs-check x (car v) S)
           (occurs-check x (cdr v) S)))
        (else #f)))))

(define ext-s-check
  (lambda (x v S)
    (cond
      ((occurs-check x v S) (values #f #f))
      (else (values (subst-add S x v) `((,x . ,v)))))))

; Returns as values the extended substitution and a list of
; associations added during the unification, or (values #f #f) if the
; unification failed.
;
; Right now appends the list of added values from sub-unifications.
; Alternatively could be threaded monadically, which could be faster
; or slower.
(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((eq? u v) (values s '()))
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let-values (((s added-car) (unify (car u) (car v) s)))
           (if s
             (let-values (((s added-cdr) (unify (cdr u) (cdr v) s)))
               (values s (append added-car added-cdr)))
             (values #f #f))))
        ((equal? u v) (values s '()))
        (else (values #f #f))))))

(define unify*
  (lambda (S+ S)
    (unify (map lhs S+) (map rhs S+) S)))


; Search

; SearchStream: #f | Procedure | State | (Pair State (-> SearchStream))

; SearchStream constructor types. Names inspired by the plus monad?

; -> SearchStream
(define mzero (lambda () #f))

; c: State
; -> SearchStream
(define unit (lambda (c) c))

; c: State
; f: (-> SearchStream)
; -> SearchStream
;
; f is a thunk to avoid unnecessary computation in the case that c is
; the last answer needed to satisfy the query.
(define choice (lambda (c f) (cons c f)))

; e: SearchStream
; -> (-> SearchStream)
(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambda () e))))

; Goal: (State -> SearchStream)

; e: SearchStream
; -> Goal
(define-syntax lambdag@
  (syntax-rules ()
    ((_ (st) e) (lambda (st) e))))

; Match on search streams. The state type must not be a pair with a
; procedure in its cdr.
;
; (() e0)     failure
; ((f) e1)    inc for interleaving. separate from success or failure
;               to ensure it goes all the way to the top of the tree.
; ((c) e2)    single result. Used rather than (choice c (inc (mzero)))
;               to avoid returning to search a part of the tree that
;               will inevitably fail.
; ((c f) e3)  multiple results.
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf)))
                 e3)))))))

; c-inf: SearchStream
;     f: (-> SearchStream)
; -> SearchStream
;
; f is a thunk to avoid unnecesarry computation in the case that the
; first answer produced by c-inf is enough to satisfy the query.
(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (inc (mplus (f) f^)))))))

; c-inf: SearchStream
;     g: Goal
; -> SearchStream
(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (inc (bind (f) g)))))))

; Int, SearchStream -> (ListOf SearchResult)
(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f)
         (() '())
         ((f) (take n f))
         ((c) (cons c '()))
         ((c f) (cons c
                  (take (and n (- n 1)) f))))))))

; -> SearchStream
(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

; -> SearchStream
(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0
                    (inc (mplus* e ...))))))

; -> Goal
(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (st)
       ; this inc triggers interleaving
       (inc
         (let ((scope (subst-scope (state-S st))))
           (let ((x (var scope)) ...)
             (bind* (g0 st) g ...))))))))


; -> Goal
(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (st)
       ; this inc triggers interleaving
       (inc
         (let ((st (state-with-scope st (new-scope))))
           (mplus*
             (bind* (g0 st) g ...)
             (bind* (g1 st) g^ ...) ...)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (take n
       (inc
         ((fresh (q) g0 g ...
            (lambdag@ (st)
              (let ((st (state-with-scope st nonlocal-scope)))
                (let ((z ((reify q) st)))
                  (choice z (lambda () (lambda () #f)))))))
          empty-state))))
    ((_ n (q0 q1 q ...) g0 g ...)
     (run n (x)
       (fresh (q0 q1 q ...)
         g0 g ...
         (== `(,q0 ,q1 ,q ...) x))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (q0 q ...) g0 g ...) (run #f (q0 q ...) g0 g ...))))


; Constraints
; C refers to the constraint store map
; c refers to an individual constraint record

; Constraint: State -> #f | State
;
; (note that a Constraint is a Goal but a Goal is not a Constraint.
;  Constraint implementations currently use this more restrained type.
;  See `and-foldl` and `update-constraints`.)

; Requirements for type constraints:
; 1. Must be positive, not negative. not-pairo wouldn't work.
; 2. Each type must have infinitely many possible values to avoid
;      incorrectness in combination with disequality constraints,
;      like: (fresh (x) (booleano x) (=/= x #t) (=/= x #f))

(define (type-constraint predicate symbol reified)
  (list predicate symbol reified))
(define type-constraint-predicate car)
(define type-constraint-symbol cadr)
(define type-constraint-reified caddr)

(define (apply-type-constraint tc)
  (lambda (u)
    (lambdag@ (st)
      (let ([type-pred (type-constraint-predicate tc)]
            [type-id (type-constraint-symbol tc)])
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
    ((_ tc-list (name predicate reified) ...)
     (begin
       (define name (apply-type-constraint (type-constraint predicate 'name 'reified)))
       ...
       (define tc-list '(reified ...))))))

(declare-type-constraints type-constraints
  (numbero number? num)
  (symbolo symbol? sym))

; Options:
;   table mapping symbol -> predicate
;   representation of type constraint as pair or struct of symbol and predicate
;   store both

(define (add-to-D st v d)
  (let* ((c (lookup-c st v))
         (c^ (c-with-D c (cons d (c-D c)))))
    (set-c st v c^)))

(define =/=*
  (lambda (S+)
    (lambdag@ (st)
      (let-values (((S added) (unify* S+ (subst-with-scope
                                           (state-S st)
                                           nonlocal-scope))))
        (cond
          ((not S) st)
          ((null? added) #f)
          (else
            ; Choose one of the disequality elements (el) to attach
            ; the constraint to. Only need to choose one because
            ; all must fail to cause the constraint to fail.
            (let ((el (car added)))
              (let ((st (add-to-D st (car el) added)))
                (if (var? (cdr el))
                  (add-to-D st (cdr el) added)
                  st)))))))))

(define =/=
  (lambda (u v)
    (=/=* `((,u . ,v)))))

;; Generalized 'absento': 'term1' can be any legal term (old version
;; of faster-miniKanren required 'term1' to be a ground atom).
(define absento
  (lambda (term1 term2)
    (lambdag@ (st)
      (let ((state (state-S st)))
        (let ((term1 (walk term1 state))
              (term2 (walk term2 state)))
          (let ((st ((=/= term1 term2) st)))
            (if st
                (cond
                  ((pair? term2)
                   (let ((st^ ((absento term1 (car term2)) st)))
                     (and st^ ((absento term1 (cdr term2)) st^))))
                  ((var? term2)
                   (let* ((c (lookup-c st term2))
                          (A (c-A c)))
                     (if (memv term1 A)
                         st
                         (let ((c^ (c-with-A c (cons term1 A))))
                           (set-c st term2 c^)))))
                  (else st))
                #f)))))))


; Fold lst with proc and initial value init. If proc ever returns #f,
; return with #f immediately. Used for applying a series of
; constraints to a state, failing if any operation fails.
(define (and-foldl proc init lst)
  (if (null? lst)
    init
    (let ([res (proc (car lst) init)])
      (and res (and-foldl proc res (cdr lst))))))

(define ==
  (lambda (u v)
    (lambdag@ (st)
      (let-values (((S added) (unify u v (state-S st))))
        (if S
          (and-foldl update-constraints (state S (state-C st)) added)
          #f)))))


; Not fully optimized. Could do absento update with fewer
; hash-refs / hash-sets.
(define update-constraints
  (lambda (a st)
    (let ([old-c (lookup-c st (lhs a))])
      (if (eq? old-c empty-c)
        st
        (let ((st (remove-c (lhs a) st)))
         (and-foldl (lambda (op st) (op st)) st
          (append
            (if (c-T old-c)
              (list ((apply-type-constraint (c-T old-c)) (rhs a)))
              '())
            (map (lambda (atom) (absento atom (rhs a))) (c-A old-c))
            (map (lambda (d) (=/=* d)) (c-D old-c)))))))))

(define walk*
  (lambda (v S)
    (let ((v (walk v S)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons (walk* (car v) S) (walk* (cdr v) S)))
        (else v)))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g g* ...)
     (lambdag@ (st)
       (let ((x (walk* x (state-S st))) ...)
         ((fresh () g g* ...) st))))))

(define succeed (== #f #f))
(define fail (== #f #t))

; Reification

; Bits from the old constraint implementation, still used for
; reification.

; In this part of the code, c refers to the
; old constraint store with components:
; S - substitution
; D - disequality constraints
; Y - symbolo
; N - numbero
; T - absento

(define (oldc S D T A)
  (list S D T A))

(define oldc-S (lambda (c) (car c)))
(define oldc-D (lambda (c) (cadr c)))
(define oldc-T (lambda (c) (caddr c)))
(define oldc-A (lambda (c) (cadddr c)))

(define (oldc-with-S c S^)
  (oldc S^ (oldc-D c) (oldc-T c) (oldc-A c)))
(define (oldc-with-D c D^)
  (oldc (oldc-S c) D^ (oldc-T c) (oldc-A c)))
(define (oldc-with-T c T^)
  (oldc (oldc-S c) (oldc-D c) T^ (oldc-A c)))
(define (oldc-with-A c A^)
  (oldc (oldc-S c) (oldc-D c) (oldc-T c) A^))

; Create a constraint store of the old representation from a state
; object, so that we can use the old reifier. Only accumulates
; constraints related to the variable being reified which makes things
; a bit faster.
(define (c-from-st st x)
  (let ((vs (vars (walk* x (state-S st)) '())))
    (foldl
      (lambda (v c-store)
        (let ((c (lookup-c st v)))
          (let ((T^ (c-T c))
                (D^ (c-D c))
                (A^ (c-A c)))
            (oldc
              (oldc-S c-store)
              (append D^ (oldc-D c-store))
              (if (c-T c)
                (begin
                  ;(display "extending:\n")
                  ;(display v)
                  ;(display "\n")
                  ;(display (c-T c))
                  ;(display "\n")
                  ;(display (subst-map-add (oldc-T c-store) v (c-T c)))
                  ;(display "\n")
                  (subst-map-add (oldc-T c-store) v (c-T c)))
                (oldc-T c-store))
              (append
                (map (lambda (absento-lhs) (cons absento-lhs v)) (c-A c))
                (oldc-A c-store))))))
      (oldc (state-S st) '() empty-subst-map '())
      (remove-duplicates vs))))

(define (vars term acc)
  (cond
    ((var? term) (cons term acc))
    ((pair? term)
     (vars (cdr term) (vars (car term) acc)))
    (else acc)))

; Simplification

(define (reify x)
  (lambda (st)

    (let* ((c (c-from-st st x))
           ;(_1 (begin
                 ;(display "before simplify:\n")
                 ;(display (oldc-T c))))
           (c (fixed-point-simplify c))
           (S (oldc-S c)))
      (let ((D (walk* (oldc-D c) S))
            (A (walk* (oldc-A c) S)))
        (let* ((v (walk* x S))
               (R (reify-S v (subst empty-subst-map nonlocal-scope)))
               (any-var-unreified? (lambda (term) (anyvar? term R))))
          (reify+ v R
                  ; Drop disequalities that are satisfiable in any
                  ; assignment of the reified variables, because
                  ; they refer to unassigned variables that are not
                  ; part of the answer, which can be assigned as needed
                  ; to satisfy the constraint.
                  (let ((D^ (remp any-var-unreified? D)))
                    (rem-subsumed d-subsumed-by? D^))
                  (oldc-T c) ; maybe need to remove unreified?
                  (let ((A^ (remp any-var-unreified? A)))
                    (rem-subsumed t-subsumed-by? A^))))))))

(define (fixed-point-simplify c)
  (define (apply-all-simplifications c)
    (foldl app1 c
           (list drop-D-b/c-T
                 move-A-to-D-b/c-a-rhs-atom
                 drop-from-D-b/c-A
                 drop-a-b/c-a-rhs-occurs-a-lhs)))
  (fixed-point apply-all-simplifications c))

(define (app1 f c) (f c))

(define (fixed-point f arg)
  (let ((r (f arg)))
    (if (eq? r arg)
      r
      (fixed-point f r))))

; Drops disequalities that are fully satisfied because the types are disjoint
; either due to type constraints or ground values.
; Examples:
;  * given (symbolo x) and (numbero y), (=/= x y) is dropped.
(define (drop-D-b/c-T c)
  (let-values (((conflicted D^)
                (partition
                  (lambda (d)
                    (exists (lambda (pr)
                              (term-ununifiable? c (lhs pr) (rhs pr)))
                            d))
                  (oldc-D c))))
              (if (not (null? conflicted))
                (oldc-with-D c D^)
                c)))

(define (term-ununifiable? c t1 t2)
  (let ((t1^ (walk t1 (oldc-S c)))
        (t2^ (walk t2 (oldc-S c))))
    (cond
      ((or (untyped-var? c t1^) (untyped-var? c t2^)) #f)
      ((var? t1^) (var-type-mismatch? c t1^ t2^))
      ((var? t2^) (var-type-mismatch? c t2^ t1^))
      (else (error 'term-ununifiable? "invariant violation")))))

(define (untyped-var? c t^)
  (and (var? t^)
       (eq? unbound (subst-map-lookup t^ (oldc-T c)))))

(define var-type-mismatch?
  (lambda (c t1^ t2^)
    (let ((t1-tc (subst-map-lookup t1^ (oldc-T c))))
      (if (var? t2^)
        (let ((t2-tc (subst-map-lookup t2^ (oldc-T c))))
          (not (eq? t1-tc t2-tc)))
        (not ((type-constraint-predicate t1-tc) t2^))))))

(define (absento->diseq t)
  (list t))

(define (move-A-to-D-b/c-a-rhs-atom c)
  (let-values (((to-move A^)
                (partition
                  (lambda (t)
                    (let ((t-rhs^ (walk (rhs t) (oldc-S c))))
                      (and (not (untyped-var? c t-rhs^))
                           (not (pair? t-rhs^)))))
                  (oldc-A c))))
    (if (not (null? to-move))
        (let ((D^ (append (map absento->diseq to-move) (oldc-D c))))
          (oldc-with-A
            (oldc-with-D c D^)
            A^))
        c)))

; Drop disequalities that are subsumed by an absento contraint,
; interpreted as a disequality.
(define (drop-from-D-b/c-A c)
  (let-values (((subsumed D^)
                (partition
                  (lambda (d)
                    (exists
                      (lambda (t)
                        (d-subsumed-by? d (absento->diseq t)))
                      (oldc-A c)))
                  (oldc-D c))))
    (if (not (null? subsumed))
      (oldc-with-D c D^)
      c)))

; Drop absento constraints that are trivially satisfied because
; any violation would cause a failure of the occurs check.
; Example:
;  (absento (list x y z) x) is trivially true because a violation would
;  require x to occur within itself.
(define (drop-a-b/c-a-rhs-occurs-a-lhs c)
  (let-values (((to-drop A^)
                (partition
                  (lambda (t)
                    (let ((t-lhs^ (walk (lhs t) (oldc-S c)))
                          (t-rhs^ (walk (rhs t) (oldc-S c))))
                      (occurs-check t-rhs^ t-lhs^ (oldc-S c))))
                  (oldc-A c))))
    (if (not (null? to-drop))
      (oldc-with-A c A^)
      c)))

(define anyvar?
  (lambda (u r)
    (cond
      ((pair? u)
       (or (anyvar? (car u) r)
           (anyvar? (cdr u) r)))
      (else (var? (walk u r))))))

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
(define (t-subsumed-by? t1 t2)
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

(define reify-S
  (lambda (v S)
    (let ((v (walk v S)))
      (cond
        ((var? v)
         (let ((n (subst-length S)))
           (let ((name (reify-name n)))
             (subst-add S v name))))
        ((pair? v)
         (let ((S (reify-S (car v) S)))
           (reify-S (cdr v) S)))
        (else S)))))

; Formatting

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define (reify+ v R D T A)
  (let ((vs (vars v '())))
    (let ((T^ (map
                (lambda (tc-type)
                  (cons tc-type
                        (filter (lambda (x) x)
                          (map
                            (lambda (v)
                              (let ((tc (subst-map-lookup v T)))
                                (and (not (eq? tc unbound))
                                     (eq? tc-type (type-constraint-reified tc))
                                     (walk* v R))))
                            (remove-duplicates vs)))))
                type-constraints)))
      ;; T^ :: (alist type-constraint-symbol (list-of reified-var))
      (form (walk* v R) (walk* D R) T^ (walk* A R)))))

(define form
  (lambda (v D T^ A)
    (let ((fd (sort-D D))
          (ft
            (filter (lambda (x) x)
                    (map
                      (lambda (p)
                        (let ((tc-type (car p)) (tc-vars (cdr p)))
                          (and (not (null? tc-vars))
                               `(,tc-type . ,(sort-lex tc-vars)))))
                      T^)))
          (fa (sort-lex A)))
      (let ((fd (if (null? fd) fd
                    (let ((fd (drop-dot-D fd)))
                      `((=/= . ,fd)))))
            (fa (if (null? fa) fa
                    (let ((fa (drop-dot fa)))
                      `((absento . ,fa))))))
        (cond
          ((and (null? fd) (null? ft) (null? fa))
           v)
          (else (append `(,v) fd ft fa)))))))

(define (sort-lex ls)
  (list-sort lex<=? ls))

(define (sort-D D)
  (sort-lex (map sort-d D)))

(define (sort-d d)
  (list-sort
    (lambda (x y)
      (lex<=? (car x) (car y)))
    (map sort-pr d)))

(define sort-pr
  (lambda (pr)
    (let ((l (lhs pr)) (r (rhs pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define lex<-reified-name?
  (lambda (r)
    (char<?
     (string-ref
      (datum->string r) 0)
     #\_)))

(define (drop-dot-D D)
  (map drop-dot D))

(define (drop-dot X)
  (map (lambda (t) (list (lhs t) (rhs t)))
       X))

(define (lex<=? x y)
  (string<=? (datum->string x) (datum->string y)))

(define (datum->string x)
  (call-with-string-output-port
    (lambda (p) (display x p))))
