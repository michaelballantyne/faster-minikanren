(load "match.scm")

(define (displayln thing)
  (display thing)
  (newline))

(define (sexp-map f sexp)
  (cond
    ((pair? sexp)
     (f (cons (sexp-map f (car sexp)) (sexp-map f (cdr sexp)))))
    (else (f sexp))))


; (Parameter (or 'naive '(assumptions <max-assumptions>))
(define mode (make-parameter 'naive))
;(define mode (make-parameter '(assumptions 1000)))

; Front-end

(define (z/assert e)
  (z/ `(assert ,e)))

(define (z/ stmt)
  (lambda (st)
    (match stmt
      [(declare-const ,v ,t)
       (match t
         [Int #t] [Real #t]
	 [,other (error 'z/ "Only Int and Real types are supported")])
       (when (not (var? v))
	 (error 'z/ "Expected logic variable in declare-const"))
       ((z/internal stmt) st)]
      [(assert ,e)
       (let* ((e^ (walk* e (state-S st)))
	      (st^ (add-varos e^ st)))
	 ((z/internal `(assert ,e^)) st^))]
      [,other (error 'z/ "Only declare-const and assert are supported")])))

(define (z/internal stmt)
  (lambda (st)
    (check
      (state-add-statement st stmt))))

; (state-M st) : (ListOf Stmts)  in reverse order.

(define (state-add-statement st stmt)
  (state-M-set st (cons stmt (state-M st))))

(define (state-statements st)
  (reverse (state-M st)))

; (Var) -> Symbol
(define (reify-v-name v)
  (string->symbol (string-append "_v" (number->string (var-idx v)))))

; (Term) -> SExpr
; replaces all miniKanren variables in a term with symbols like _v0 for the solver.
(define (reify-to-smt-symbols e)
  (sexp-map
    (lambda (sexp)
      (if (var? sexp)
        (reify-v-name sexp)
        sexp))
    e))

(define (wrap-neg e)
  (sexp-map
    (lambda (sexp)
      (if (and (number? sexp) (< sexp 0))
          `(- ,(- sexp))
          sexp))
    e))

;; Back-end

; State; initialized in `z/reset!`

; Int for GC and assumption naming
(define assumption-count #f)

; Assm = Symbol
; (ListOf Assm)
(define all-assumptions #f)

; SMTType = (or 'Int 'Real)
; (SubstMap SMTType)
(define declared-types #f)

; (AList ReifiedAssertion Assm)
(define assertion-to-assumption #f)

; (AList Symbol MkVar)
(define relevant-smtvar-to-mkvar #f)


(define (z/reset!)
  (call-z3 '((reset)))
  (set! assumption-count 0)
  (set! all-assumptions '())
  (set! declared-types empty-subst-map)
  (set! assertion-to-assumption '())
  (reset-relevant-smtvars!))


(define (fresh-assumption!)
  (define assm
    (string->symbol
      (string-append "_a" (number->string assumption-count))))
  (set! assumption-count (+ assumption-count 1))
  (set! all-assumptions (cons assm all-assumptions))
  (match (mode)
    [(assumptions ,_)
     (call-z3 `((declare-const ,assm Bool)))]
    [,_ (void)])
  assm)


(define (add-assertion-to-assumption! e assm)
  (set! assertion-to-assumption
    (cons (cons e assm) assertion-to-assumption)))


(define (reset-relevant-smtvars!)
  (set! relevant-smtvar-to-mkvar '()))

(define (record-relevant-smtvars! e)
  (for-each
    (lambda (v)
      (let ([smt-var (reify-v-name v)])
        (when (not (assoc smt-var relevant-smtvar-to-mkvar))
          (set! relevant-smtvar-to-mkvar
            (cons (cons smt-var v) relevant-smtvar-to-mkvar)))))
    (vars e '())))



(define (check st)
  (define all-stmts (state-statements st))

  ; I hate the side effects on this var!
  (reset-relevant-smtvars!)

  (match (mode)
    [naive
      (z/reset!)
      (replay! all-stmts)
      (z/check-sat)]
    [(assumptions ,max-assms)
     (when (> assumption-count max-assms)
       (printf "gc z3...\n")
       (z/reset!))
     (let ([assms (replay! all-stmts)])
       (z/check-sat-assuming assms))])

  (if (read-sat)
    st
    #f))

(define (replay! all-statements)
  (define assms '())
  (define (add-assm! assm)
    (set! assms (cons assm assms)))

  (for-each
    (lambda (stmt)
      (match stmt
        [(declare-const ,v ,t)
         (ensure-declared! v t)]
        [(assert ,e)
         (record-relevant-smtvars! e)
         (add-assm! (ensure-assert! e))]))
    all-statements)

  assms)

(define (declared-type v)
  (let ([t (subst-map-lookup v declared-types)])
    (if (eq? t unbound)
      #f
      t)))

(define (ensure-declared! v as-type)
  (let ([existing-decl-type (declared-type v)])
    (cond
      [(not existing-decl-type)
       (set! declared-types (subst-map-add declared-types v as-type))
       (call-z3 `((declare-const ,(reify-to-smt-symbols v) ,as-type)))]
      [(eq? as-type existing-decl-type)
       (void)]
      [else (error 'z/ "Inconsistent SMT types")])))


; (SMTExpr) -> Assm
; Returns the assumption variable corresponding to the
;  assertion.
(define (ensure-assert! e)

  (match (assoc e assertion-to-assumption)
    [(,_ . ,assm)
     assm]
    [#f
     (define e^ (wrap-neg (reify-to-smt-symbols e)))
     (define assm (fresh-assumption!))
     (add-assertion-to-assumption! e assm)
     (for-each
       (lambda (v)
         (when (not (declared-type v))
           (ensure-declared! v 'Int)))
       (vars e '()))
     (match (mode)
            [naive
              (call-z3 `((assert ,e^)))]
            [(assumptions ,_)
             (call-z3 `((assert (=> ,assm ,e^))))])
     assm]))

(define (z/check-sat)
  (call-z3 '((check-sat))))

(define (z/check-sat-assuming a)
  (call-z3 `((check-sat-assuming
               ,(pos-assms->all-literals a)))))

; In my testing with z3, this doesn't appear to help vs just asserting the positives
(define (pos-assms->all-literals pos)
  (map (lambda (b)
         (if (memq b pos)
           b
           `(not ,b)))
       all-assumptions))


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
        (z/internal
         `(assert
            (and
              ,@(map
                  (lambda (cs)
                    `(or
                       ,@(map
                           (lambda (ds)
                             `(not (= ,(car ds) ,(cdr ds))))
                           cs)))
                  as))))
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

(define (add-varos e st)
  (foldl (lambda (v st)
           (bind
             st
             (z/varo v)))
          st
          (vars e '())))

(define z/purge
  (lambdag@ (st)
    (let ((M (state-M st)))
      (if (null? M)
          st
          (let loop-g ([st^ st])
            (let ([m (check/relevant-model st^)])
              (if (not m)
                (mzero)
                ((conde
                   [(add-model m)]
                   [(assert-neg-model m)
                    loop-g])
                 st^))))))))

; Model = (Alist Var Number)
; (State) -> (or #f Model)
; EFFECT:
;   solver state
;   relevant-smtvar-to-mkvar
(define (check/relevant-model st)
  (and (check st) (get-relevant-model)))

; EFFECT
(define (get-relevant-model)
  (filter (lambda (p) (var? (car p)))
          (smt-symbols-to-vars (get-model-inc))))

; EFFECT
(define (smt-symbols-to-vars e)
  (sexp-map
    (lambda (sexp)
      (cond
        [(and (symbol? sexp)
              (assoc sexp relevant-smtvar-to-mkvar))
         => (lambda (p) (cdr p))]
        [else sexp]))
    e))

; (Model) -> State
; Pure
(define add-model
  (lambda (m)
    (lambdag@ (st)
      (foldl (lambda (p st)
               (let-values (((S _) (unify (lhs p) (rhs p) (state-S st))))
                 (when (not S)
                   (error 'add-model "model fails mK constraints; mk constraints not soundly reflected to SMT"))
                 (state-S-set st S)))
             st
             m))))

; (Model) -> Goal
; Pure
(define (assert-neg-model m)
  (if (null? m)
    fail
    (lambda (st) (state-add-statement st (neg-model m)))))





