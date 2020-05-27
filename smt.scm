(load "match.scm")

; (Parameter (or 'naive '(assumptions <max-assumptions>))
(define mode (make-parameter 'naive))
;(define mode (make-parameter '(assumptions 1000)))

(define (displayln thing)
  (display thing)
  (newline))

; (((SExp) -> SExp) SExp) -> SExp
; Pure
(define (sexp-map f sexp)
  (cond
    ((pair? sexp)
     (f (cons (sexp-map f (car sexp)) (sexp-map f (cdr sexp)))))
    (else (f sexp))))

; Front-end
;
; Maintains the invariant that miniKanren constraints relevant to SMT variables
; are reflected as solver constraints. Owns c-M.
;
; All interaction with back-end happens via z/internal. Does not directly
; access solver or back-end state.
;
; interface: z/assert, z/, z/add-equality, z/add-disequality

; (SMTExpr) -> Goal
(define (z/assert e)
  (z/ `(assert ,e)))

; (Stmt) -> Goal
(define (z/ stmt)
  (match stmt
    [(declare-const ,v ,t)
     (match t
       [Int #t] [Real #t]
       [,other (error 'z/ "Only Int and Real types are supported")])
     (when (not (var? v))
       (error 'z/ "Expected logic variable in declare-const"))
     (z/internal stmt)]
    [(assert ,e)
     (lambdag@ (st)
       (let ((e^ (walk* e (state-S st))))
         (bind
           (add-varos e^ st)
           (z/internal `(assert ,e^)))))]
    [,other (error 'z/ "Only declare-const and assert are supported")]))

; (SMTExpr State) -> (or #f State)
(define (add-varos e st)
  (foldl (lambda (v st)
           (bind
             st
             (z/varo v)))
          st
          (vars e '())))

; (MkVar) -> Goal
(define (z/varo u)
  (lambdag@ (st)
    (let ((term (walk u (state-S st))))
      (if (var? term)
          (let* ((c (lookup-c term st))
                 (M (c-M c))
                 (D (c-D c)))
            (if M
              st
              (z/add-disequality
                (set-c term (c-with-M c #t) st)
                D)))
          st))))

; (MkVar Term) -> Goal
(define (z/add-equality v t)
  (lambdag@ (st)
    (bind
      ((z/internal `(assert (= ,v ,t))) st)
      (z/varo t))))

; (State (AList MkVar Term)) -> (or #f State)
(define (z/add-disequality st D)
  (let ((as (filter-smt-ok? st D)))
    (if (not (null? as))
        ((z/internal
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
          st)
        st)))

; (State (AList MkVar Term)) -> (AList MkVar Term)
; Pure
(define (filter-smt-ok? st D)
  (filter
   (lambda (cs)
     (for-all (lambda (ds)
                (and (smt-ok? st (car ds)) (smt-ok? st (cdr ds))))
              cs))
   D))

; (State Term) -> Bool
; Pure
(define (smt-ok? st x)
  (let ((x (walk* x (state-S st))))
    (or (number? x)
        (and (var? x)
             (let ((c (lookup-c x st)))
               (c-M c))))))


; Back-end
;
; Owns state-M.
;
; interface: z/internal, z/reset, z/purge

; ((ListOf Stmt)) -> Goal
(define (z/internal stmt)
  (lambda (st)
    (check
      (state-add-statement st stmt))))

; (state-M st) : (ListOf Stmt)  in reverse order.

(define (state-add-statement st stmt)
  (state-M-set st (cons stmt (state-M st))))

; (State) -> (ListOf Stmt)
; Pure
(define (state-statements st)
  (reverse (state-M st)))

; (Var) -> Symbol
; Pure
(define (reify-v-name v)
  (string->symbol (string-append "_v" (number->string (var-idx v)))))

; (Term) -> SExpr
; Pure
; replaces all miniKanren variables in a term with symbols like _v0 for the solver.
(define (reify-to-smt-symbols e)
  (sexp-map
    (lambda (sexp)
      (if (var? sexp)
        (reify-v-name sexp)
        sexp))
    e))

; SMTExpr -> SMTExpr
; Pure
(define (wrap-neg e)
  (sexp-map
    (lambda (sexp)
      (if (and (number? sexp) (< sexp 0))
          `(- ,(- sexp))
          sexp))
    e))

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

; () -> Void
(define (z/reset!)
  (call-z3 '((reset)))
  (set! assumption-count 0)
  (set! all-assumptions '())
  (set! declared-types empty-subst-map)
  (set! assertion-to-assumption '())
  (reset-relevant-smtvars!))

; () -> Assm
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

; (SMTExpr Assm) -> Void
(define (add-assertion-to-assumption! e assm)
  (set! assertion-to-assumption
    (cons (cons e assm) assertion-to-assumption)))

; () -> Void
(define (reset-relevant-smtvars!)
  (set! relevant-smtvar-to-mkvar '()))

; (SMTExpr) -> Void
(define (record-relevant-smtvars! e)
  (for-each
    (lambda (v)
      (let ([smt-var (reify-v-name v)])
        (when (not (assoc smt-var relevant-smtvar-to-mkvar))
          (set! relevant-smtvar-to-mkvar
            (cons (cons smt-var v) relevant-smtvar-to-mkvar)))))
    (vars e '())))



; (State) -> (or #f State)
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

; ((ListOf Stmt)) -> (ListOf Assm)
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

; (MkVar) -> (or #f SMTType)
(define (declared-type v)
  (let ([t (subst-map-lookup v declared-types)])
    (if (eq? t unbound)
      #f
      t)))

; (MkVar SMTType) -> Void
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

; () -> Void
(define (z/check-sat)
  (call-z3 '((check-sat))))

; ((ListOf Assm)) -> Void
(define (z/check-sat-assuming a)
  (call-z3 `((check-sat-assuming
               ,(pos-assms->all-literals a)))))

; ((ListOf Assm)) -> (ListOf SMTExpr)
; In my testing with z3, this doesn't appear to help vs just asserting the positives
(define (pos-assms->all-literals pos)
  (map (lambda (b)
         (if (memq b pos)
           b
           `(not ,b)))
       all-assumptions))


; Goal
(define z/purge
  (lambdag@ (st)
    (if (null? (state-M st))
      st
      (let loop-g ([st^ st])
        (let ([m (check/relevant-model st^)])
          (if (not m)
            (mzero)
            ((conde
               [(add-model m)]
               [(assert-neg-model m)
                loop-g])
             st^)))))))

; Model = (Alist Var Number)
; (State) -> (or #f Model)
(define (check/relevant-model st)
  (and (check st) (get-relevant-model)))

; () -> Model
(define (get-relevant-model)
  (filter (lambda (p) (var? (car p)))
          (smt-symbols-to-vars (get-model-inc))))

; SExp -> SExp
(define (smt-symbols-to-vars e)
  (sexp-map
    (lambda (sexp)
      (cond
        [(and (symbol? sexp)
              (assoc sexp relevant-smtvar-to-mkvar))
         => (lambda (p) (cdr p))]
        [else sexp]))
    e))

; (Model) -> Goal
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

