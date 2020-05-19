(load "match.scm")


; For avoiding duplicate declares, need an (IntMap SMTType)
; Processing an assert will add a declare to Int if there isn't
;  already a declare.
; Processing a declaration will add the declare if there isn't one
;  or if it matches; if it doesn't match, we raise an error.
;
; In the version using check-sat-assuming, declarations will need
;   to be globally consistent, not just per-path consistent.
;   This is because we'll be keeping assertions from other paths
;   as part of the SMT problem, though qualified by assumptions.
; Thus, this map will need to be global, not part of the constraint
;  store or recomputed per-check.


; There are two other kinds of deduplication:
;  - Avoiding repeated identical assertions to simplify the problem, even when explicitly written by programmers.
;  - In the check-sat-assuming version: only asserting new constraints, not those previously asserted by other threads.
;
; These could perhaps be combined. Given we're not providing the And / Or tree it is safe to equate constraints in
; different positions.
;
; How would assigning assumption IDs work then?
;   Could happen after deduplication? Maybe a hashmap from assertion text to assumption ID?
;
; This can be after the upper logical layer has detected inconsistencies, reified logic vars, walk*'ed, etc.
;
; Constraint store could contain constraints without assumption IDs. Each time we'd figure what's new
;   and assign assumptions again.
;
; Ideally we would have a way of only look at new stuff or stuff that has to be replayed due to a GC.
;  But it seems likely that this won't matter, as the SMT calls will be much more expensive.
;
; I think deduping declarations can happen in the same pass, though it will use a different map as it needs to
; know a type rather than an assumption ID.

; Difference between naive and assumptions versions:
;   naive resets every time before or after checking
;   naive emits asserts without assumption guards
;   naive does check-sat, not check-sat-assuming.

; What can we reuse of the old impl?
;   z/varo
;   probably z/purge
;   reify-to-smt-symbols

; z/check just takes in state-M, (re)plays
;   in check-sat-assuming mode it accumulates the list of assumptions that assertions resolve to
;   and uses that list in check-sat-assuming

; Other things reify, add to state-M, then call z/check if ready.


; (Parameter (or 'naive '(assumptions <max-assumptions>))
(define mode (make-parameter 'naive))

; SMTType = (or 'Int 'Real)
; (IntMap SMTType)
(define declared-types )


; Assm = Symbol

; (ListOf Assm)
(define all-assumptions )

; (AList ReifiedAssertion Assm)
(define assertion-to-assumption )

; Int x where 0 <= x < max-assumptions
;   for GC and assumption naming
(define assumption-count )


; Front-end

(define (z/assert e)
  (z/ `(assert ,e)))


(define (z/ stmt)

  (match stmt
    [(declare-const ,v ,t)
     ]
    [(assert ,e)
     ])

  (walk* )

  )

; (Var) -> Symbol
(define (reify-v-name v)
  (string->symbol (string-append "_v" (number->string (var-idx v)))))

; (Term) -> SExpr
; replaces all miniKanren variables in a term with symbols like _v0 for the solver.
(define (reify-to-smt-symbols v)
  (cond
    ((var? v) (reify-v-name v))
    ((pair? v)
     (cons (reify-to-smt-symbols (car v)) (reify-to-smt-symbols (cdr v))))
    (else v)))

(define (pos-assms->all-literals pos)
  (map (lambda (b)
         (if (memq b pos)
           b
           `(not ,b)))
       all-assumptions))

(define (check-sat-assuming a m)
  (replay-if-needed a m)
  (call-z3 `((check-sat-assuming ,(get-assumptions a))))
  (read-sat))

(define (smt-ok? st x)
  (let ((x (walk* x (state-S st))))
    (or (number? x)
        (and (var? x)
             (let ((c (lookup-c x st)))
               (c-M c))))))

(define (filter-smt-ok? st D)
  (filter
   (lambda (cs)
     (for-all (lambda (ds)
                (and (smt-ok? st (car ds)) (smt-ok? st (cdr ds))))
              cs))
   D))

(define (add-smt-disequality st D)
  (let ((as (filter-smt-ok? st D)))
    (if (not (null? as))
        (z/assert
         `(and
           ,@(map
              (lambda (cs)
                `(or
                  ,@(map
                     (lambda (ds)
                       `(not (= ,(car ds) ,(cdr ds))))
                     cs)))
              as))
         #t)
        (lambdag@ (st) st))))

(define z/varo
  (lambda (u)
    (lambdag@ (st)
      (let ((term (walk u (state-S st))))
        (if (var? term)
            (let* ((c (lookup-c term st))
                   (M (c-M c))
                   (D (c-D c)))
              (bind*
               st
               (lambdag@ (st)
                 (if M st
                     (set-c term (c-with-M c #t) st)))
               (if (or M (null? D))
                   (lambdag@ (st) st)
                   (lambdag@ (st) ((add-smt-disequality st D) st)))))
            st)))))

(define global-buffer '())
(define z/global
  (lambda (lines)
    (call-z3 lines)
    (set! global-buffer (append global-buffer lines))))
(define local-buffer '())
(define z/local
  (lambda (lines)
    (lambdag@ (st)
      (begin
        (set! local-buffer (append local-buffer lines))
        (call-z3 lines)
        (let ((M (append (reverse lines) (state-M st))))
          (state-with-M st M))))))

; Ah. So replay is repeating some of the same work as reify-SM is, but on post-reified content:
;    declare Int for undeclared vars in assms
;    avoid replaying dup decls
;    adding assumptions to all-assumptions as they are re-declared

(define (replay-if-needed a m)
  (let ((r (filter (lambda (x) (not (member x local-buffer))) m)))
    (unless (null? r)
      (let ((lines (reverse r)))
        (let ((new-decls  (filter (lambda (x)
                                    (and (declares? x)
                                         (not (eq? (caddr x) 'Bool))))
                                  lines))
              (new-assumptions (filter (lambda (x)
                                         (and (declares? x)
                                              (eq? (caddr x) 'Bool)))
                                       lines))
              (other-lines (filter (lambda (x) (not (declares? x))) lines)))
          (let* ((undeclared-decls (filter (lambda (x) (undeclared? (cadr x))) new-decls))
                 (undeclared-assumptions (filter (lambda (x) (undeclared? (cadr x))) new-assumptions))
                 (actual-lines (append undeclared-decls undeclared-assumptions other-lines)))
            (let* ((rs (filter undeclared? (map reify-v-name (cdr (assq a relevant-vars)))))
                   (undeclared-rs (map (lambda (x) `(declare-const ,x Int)) rs))
                   (actual-lines (append undeclared-rs actual-lines)))
              (set! all-assumptions (append (map cadr undeclared-assumptions) all-assumptions))
              (set! local-buffer (append local-buffer actual-lines))
              (call-z3 actual-lines))))))))

(define (z/check m a no_walk?)
  (lambdag@ (st)
    (begin
      (replay-if-needed (last-assumption (state-M st)) (state-M st))
      (let ((r (wrap-neg ((z/reify-SM m no_walk?) st))))
        (z/global (car r))
        (bind*
         st
         (z/local (cadr r))
         (lambdag@ (st)
           (if (and a (check-sat-assuming a (state-M st)))
               (begin
                 (let ((p (assq a relevant-vars)))
                   ;;(set-cdr! p (append (caddr r) (cdr p)))
                   (set! relevant-vars (cons (cons a (append (caddr r) (cdr p))) (remove p relevant-vars))))
                 ((let loop ((vs (caddr r)))
                    (lambdag@ (st)
                      (if (null? vs)
                          st
                          (bind*
                           st
                           (numbero (car vs))
                           (z/varo (car vs))
                           (loop (cdr vs))))))
                  st))
               (if a #f st))))))))

(define (z/ line)
  (z/check (list line) #f #t))

(define assumption-count 0)
(define (fresh-assumption)
  (when (and (= (remainder assumption-count 1000) 0)
             (> assumption-count 0))
    (printf "gc z3...\n")
    (z/gc!))
  (set! assumption-count (+ assumption-count 1))
  (string->symbol ;(format #f "_a~d" assumption-count)
   (string-append "_a" (number->string assumption-count))
                  ))

(define (last-assumption m)
  (let ((r (filter (lambda (x) (and (pair? x)
                               (eq? 'assert (car x))
                               (pair? (cadr x))
                               (eq? (car (cadr x)) '=>)))
                   m)))
    (if (null? r)
        'true
        (cadr (cadr (car r))))))

(define (wrap-neg e)
  (if (number? e)
      (if (< e 0)
	  `(- ,(- e))
	  e)
      (if (pair? e)
	  (cons (wrap-neg (car e)) (wrap-neg (cdr e)))
	  e)))

(define z/assert
  (lambda (e . args)
    (let ((no_walk? (and (not (null? args)) (car args))))
      (lambdag@ (st)
        (let ((a1 (fresh-assumption)))
          (let ((a0 (last-assumption (state-M st))))
            (let ((rs (if (eq? a0 'true) '()  (cdr (assq a0 relevant-vars))))
                  (as (if (eq? a0 'true) '() (assq a0 assumption-chains))))
              (set! relevant-vars (cons (cons a1 rs) relevant-vars))
              (set! assumption-chains (cons (cons a1 as) assumption-chains))
              (set! all-assumptions (cons a1 all-assumptions))
              (bind*
               st
               (z/check `((assert (=> ,a1 ,e))
                          (declare-const ,a1 Bool))
                        a1
                        no_walk?)))))))))

(define relevant-vars '())
(define assumption-chains '())
(define all-assumptions '())
(define (z/reset!)
  (call-z3 '((reset)))
  (set! decls '())
  (set! relevant-vars '())
  (set! assumption-chains '())
  (set! all-assumptions '())
  (set! assumption-count 0)
  (set! m-subst-map empty-subst-map)
  (set! global-buffer '())
  (set! local-buffer '()))
(define (z/gc!)
  (call-z3 '((reset)))
  (call-z3 global-buffer)
  (set! decls '())
  (set! all-assumptions '())
  (set! local-buffer '()))

(define add-model
  (lambda (m)
    (lambdag@ (st)
      (if (null? m)
          st
          (bind*
           st
           (== (caar m) (cdar m))
           (add-model (cdr m)))))))

(define assert-neg-model
  (lambda (m)
    (let* ([m
            (filter (lambda (x) ; ignoring functions
                      (or (number? (cdr x))
                          (symbol? (cdr x)) ; for bitvectors
                          )) m)])
      (if (null? m)
          fail
          (z/assert (cadr (neg-model m)))))))

(define z/purge
  (lambdag@ (st)
    (let ((M (state-M st)))
      (if (null? M)
          st
          (let ([a (last-assumption (state-M st))])
            (if (eq? a 'true)
                st
                (if (not (check-sat-assuming a (state-M st)))
                    #f
                    (let ([rs (map (lambda (x) (cons (reify-v-name x) x)) (cdr (assq a relevant-vars)))])
                      ((let loop ()
                         (lambdag@ (st)
                           (let ((m (get-model-inc)))
                             (let ((m (map (lambda (x) (cons (cdr (assq (car x) rs)) (cdr x))) (filter (lambda (x) (assq (car x) rs)) m))))
                               (let ((st (state-with-scope st (new-scope))))
                                 (mplus*
                                  (bind*
                                   (state-with-M st '())
                                   (add-model m))
                                  (bind*
                                   st
                                   (assert-neg-model m)
                                   (loop))))))))
                       st)))))))))
