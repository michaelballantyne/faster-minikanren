(load "match.scm")

(define (displayln thing)
  (display thing)
  (newline))

; (Parameter (or 'naive '(assumptions <max-assumptions>))
;(define mode (make-parameter 'naive))
(define mode (make-parameter '(assumptions 1000)))

; Front-end

(define (z/assert e)
  (z/ `(assert ,e)))

(define (z/ stmt)
  (lambda (st)
    (define reified
      (begin
      (match stmt
        [(declare-const ,v ,t)
         (match t
           [Int #t] [Real #t]
           [,other (error 'z/ "Only Int and Real types are supported")])
         (when (not (var? v))
           (error 'z/ "Expected logic variable in declare-const"))
         stmt]
        [(assert ,e)
         `(assert ,(wrap-neg (walk* e (state-S st))))]
        [,other (error 'z/ "Only declare-const and assert are supported")])))

    ((z/internal reified) st)))

(define (z/internal stmt)
  (lambda (st)
    (check
      (state-add-statement st stmt))))

; (state-M st) : (ListOf Stmts)  in reverse order.

(define (state-add-statement st stmt)
  (state-with-M st (cons stmt (state-M st))))

(define (state-statements st)
  (reverse (state-M st)))

; (Var) -> Symbol
(define (reify-v-name v)
  (string->symbol (string-append "_v" (number->string (var-idx v)))))

; (Term) -> SExpr
; replaces all miniKanren variables in a term with symbols like _v0 for the solver.
(define (reify-to-smt-symbols v)
  (cond
    ((var? v)
     (set! smtvar-to-mkvar (cons (cons (reify-v-name v) v) smtvar-to-mkvar))
     (reify-v-name v))
    ((pair? v)
     (cons (reify-to-smt-symbols (car v)) (reify-to-smt-symbols (cdr v))))
    (else v)))

(define (wrap-neg e)
  (if (number? e)
      (if (< e 0)
	  `(- ,(- e))
	  e)
      (if (pair? e)
	  (cons (wrap-neg (car e)) (wrap-neg (cdr e)))
	  e)))

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

(define smtvar-to-mkvar #f)


(define (z/reset!)
  (call-z3 '((reset)))
  (set! assumption-count 0)
  (set! all-assumptions '())
  (set! declared-types empty-subst-map)
  (set! assertion-to-assumption '())
  (set! smtvar-to-mkvar '()))

(define (fresh-assumption!)
  (define assm
    (string->symbol
      (string-append "_a" (number->string assumption-count))))
  (set! assumption-count (+ assumption-count 1))
  (set! all-assumptions (cons assm all-assumptions))
  (call-z3 `((declare-const ,assm Bool)))
  assm)

(define (add-assertion-to-assumption! e assm)
  (set! assertion-to-assumption
    (cons (cons e assm) assertion-to-assumption)))


(define (check st)
  (define all-stmts (state-statements st))

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
     (define assm (fresh-assumption!))
     (add-assertion-to-assumption! e assm)
     (for-each
       (lambda (v)
         (when (not (declared-type v))
           (ensure-declared! v 'Int)))
       (vars e '()))
     (match (mode)
            [naive
              (call-z3 `((assert ,(reify-to-smt-symbols e))))]
            [(assumptions ,_)
             (call-z3 `((assert (=> ,assm ,(reify-to-smt-symbols e)))))])
     assm]))

(define (z/check-sat)
  (call-z3 '((check-sat))))

(define (z/check-sat-assuming a)
  (call-z3 `((check-sat-assuming
               ,(pos-assms->all-literals a)))))

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

(define add-model
  (lambda (m)
    (lambdag@ (st)
      (cond
        [(null? m) st]
        [(assoc (caar m) smtvar-to-mkvar)
         => (lambda (p)
          (bind*
           st
           (== (cdr p) (cdar m))
           (add-model (cdr m))))]
        [else ((add-model (cdr m)) st)]
         ))))

(define assert-neg-model
  (lambda (m)
    (let* ([m
            (filter (lambda (x) ; ignoring functions
                      (or (number? (cdr x))
                          (symbol? (cdr x)) ; for bitvectors
                          )) m)])
      (if (null? m)
          fail
          (z/internal `(assert ,(cadr (neg-model m))))))))

(define z/purge
  (lambdag@ (st)
    (let ((M (state-M st)))
      (if (null? M)
          st
          (if (not (check st))
              #f
              ((let loop ()
                 (lambdag@ (st)
                           (let ((m (get-model-inc)))
                             (let ((st (state-with-scope st (new-scope))))
                               (mplus*
                                 (bind*
                                   (state-with-M st '())
                                   (add-model m))
                                 (bind*
                                   st
                                   (assert-neg-model m)
                                   (loop)))))))
              st))))))
