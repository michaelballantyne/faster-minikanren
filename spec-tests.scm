; unification bits
(define (simple-ext-s-check x v S)
  (if (occurs-check x v S)
    #f
    (subst-add S x v)))

(define (simple-ext-s-no-check x v S)
  (subst-add S x v))


; test infrastructure
(define loop-count 10000000)

(define (test-loop-f f)
  (let loop ([i loop-count])
    (if (= i 0)
      (void)
      (let ([res (f)])
        (and res
             (loop (- i 1)))))))
(define-syntax test-loop
  (syntax-rules () [(_ e) (test-loop-f (lambda () e))]))

(define-syntax time-test-variants
  (syntax-rules ()
    [(_ description (impl ...) (call args ...))
     (let ()
       (display description)
       (display ":\n\n")

       (let ()
         (display 'impl)
         (display "\n")
         ; run once to print the result
         (display (impl args ...))
         (display "\n")
         ; run many times for timing
         (time (test-loop (impl args ...)))
         (display "\n"))
       ...)]))

; Example 1 to compile:
;
; (lambda (a)
;   (fresh (b c)
;     (== a (list b c))))
;
; Implementations follow...


;;;
;;; ex1-unify
;;;

; Implementation with plain 'ol unify

(define (ex1-unify a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)]
         [b (var sc)]
         [c (var sc)])
    (let-values
      ([(r1 r2)
        (unify a `(,b ,c) S)])
      r1)))



;;;
;;; ex1-manual-continuations
;;;

; Manually compiled with let-bound continuations. Notice p2-match-k and p2-cons-k need to take
; previously matched `b` as an argument as it isn't in scope.

(define (ex1-manual-continuations a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)])
    (let* ([body (lambda (b c S^)
                   S^)]
           [lit-cons-k (lambda (v^ b c)
                         (let ([S^ (simple-ext-s-no-check v^ '() S)])
                           (body b c S^)))]
           [p2-cons (lambda ()
                      (let ([c (var sc)])
                        (values c (cons c '()))))]
           [p1-cons (lambda ()
                      (let ([b (var sc)])
                        (let-values ([(c t) (p2-cons)])
                          (values b c (cons b t)))))]
           [p2-cons-k (lambda (v^ b)
                        (let-values ([(c res) (p2-cons)])
                          (let ([S^ (simple-ext-s-no-check v^ res S)])
                            (body b c S^))))]
           [p2-match-k (lambda (c t3 b)
                         (let ([v^ (walk t3 S)])
                           (cond
                             [(var? v^) (lit-cons-k v^ b c)]
                             [(equal? v^ '())
                              (body b c S)]
                             [else #f])))]
           [p1-cons-k (lambda (v^)
                        (let-values ([(b c res) (p1-cons)])
                          (let ([S^ (simple-ext-s-no-check v^ res S)])
                            (body b c S^))))]
           [p1-match-k (lambda (b t2)
                         (let ([v^ (walk t2 S)])
                           (cond
                             [(var? v^) (p2-cons-k v^ b)]
                             [(pair? v^) (p2-match-k (car v^) (cdr v^) b)]
                             [else #f])))])
      (let ([v^ (walk a S)])
        (cond
          [(var? v^) (p1-cons-k v^)]
          [(pair? v^) (p1-match-k (car v^) (cdr v^))]
          [else #f])))))

;;;
;;; ex1-manual-direct
;;;

; Manually compiled without continuations; we don't need to pass along previously-matched
; variables this way, until the final call to `body`.

(define (ex1-manual-direct a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)])
    (let ([body (lambda (b c S^) S^)])
      (let ([p2-cons (lambda ()
                       (let ([c (var sc)])
                         (values (cons c '()) c)))])
        (let ([p1-cons (lambda ()
                         (let ([b (var sc)])
                           (let-values ([(t c) (p2-cons)])
                              (values (cons b t) b c))))])
          (let ([v^ (walk a S)])
            (cond
              [(var? v^)
               (let-values ([(res b c) (p1-cons)])
                           (let ([S^ (simple-ext-s-no-check v^ res S)])
                             (body b c S^)))]
              [(pair? v^)
               (let ([b (car v^)] [t2 (cdr v^)])
                 (let ([v^ (walk t2 S)])
                   (cond
                     [(var? v^)
                      (let-values ([(res c) (p2-cons)])
                                  (let ([S^ (simple-ext-s-no-check v^ res S)])
                                    (body b c S^)))]
                     [(pair? v^)
                      (let ([c (car v^)] [t3 (cdr v^)])
                        (let ([v^ (walk t3 S)])
                          (cond
                            [(var? v^)
                             (let ([S^ (simple-ext-s-no-check v^ '() S)])
                               (body b c S^))]
                            [(equal? v^ '())
                             (body b c S)]
                            [else #f])))]
                     [else #f])))]
              [else #f])))))))


;;;
;;; ex1-macros-direct
;;;

; Abstract over the pattern from ex1-manual-direct a bit with some macros

(define-syntax mmatch-pair
  (syntax-rules ()
    [(_ v                    ; value to match
        S                    ; substitution to walk in
        [v^ e-c]             ; if fresh, bind v^ and run e-c
        [(a d) e-m])         ; if match, bind a to car and d to cdr and run e-m
     (let ([v^ (walk v S)])
       (cond
         [(var? v^) e-c]
         [(pair? v^)
          (let ([a (car v^)] [d (cdr v^)])
            e-m)]
         [else #f]))]))


(define-syntax mmatch-lit
  (syntax-rules ()
    [(_ v                     ; value to match
        S                     ; substitution to walk in
        lit                   ; expected literal
        [v^ e-c]              ; if fresh, bind v^ and run e-c
        [e-m])                ; if match, run e-m
     (let ([v^ (walk v S)])
       (cond
         [(var? v^) e-c]
         [(equal? v^ '()) e-m]
         [else #f]))]))

(define (ex1-macros-direct a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)])
    (let ([body (lambda (b c S^) S^)])
      (let ([p2-cons (lambda ()
                       (let ([c (var sc)])
                         (values (cons c '()) c)))])
        (let ([p1-cons (lambda ()
                         (let ([b (var sc)])
                           (let-values ([(t c) (p2-cons)])
                              (values (cons b t) b c))))])
          (mmatch-pair a S
            [v^ (let-values ([(res b c ) (p1-cons)])
                  (let ([S^ (simple-ext-s-no-check v^ res S)])
                    (body b c S^)))]
            [(b t2)
             (mmatch-pair t2 S
               [v^ (let-values ([(res c) (p2-cons)])
                     (let ([S^ (simple-ext-s-no-check v^ res S)])
                       (body b c S^)))]
               [(c t3)
                (mmatch-lit t3 S '()
                  [v^ (let ([S^ (simple-ext-s-no-check v^ '() S)])
                        (body b c S^))]
                  [(body b c S)])])]))))))


;;;
;;; ex1-functions-direct
;;;

; Try abstracting over the pattern with functions, rather than macros. Helpful
; to evaluate the runtime cost.

(define (match-pair v S k-c k-m)
  (let ([v^ (walk v S)])
    (cond
      [(var? v^) (k-c v^)]
      [(pair? v^)
       (k-m (car v^) (cdr v^))]
      [else #f])))

(define (match-literal v S lit k-c k-m)
  (let ([v^ (walk v S)])
    (cond
      [(var? v^) (k-c v^)]
      [(equal? v^ lit)
       (k-m)]
      [else #f])))

(define (ex1-functions-direct a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)])
    (let* ([body (lambda (b c S^) S^)]
           [p2-cons (lambda ()
                      (let ([c (var sc)])
                        (values c (cons c '()))))]
           [p1-cons (lambda ()
                      (let ([b (var sc)])
                        (let-values ([(c t) (p2-cons)])
                          (values b c (cons b t)))))])
      (match-pair
        a S
        (lambda (v^)
          (let-values ([(b c res) (p1-cons)])
            (let ([S^ (simple-ext-s-no-check v^ res S)])
              (body b c S^))))
        (lambda (b t2)
          (match-pair
            t2 S
            (lambda (v^)
              (let-values ([(c res) (p2-cons)])
                (let ([S^ (simple-ext-s-no-check v^ res S)])
                  (body b c S^))))
            (lambda (c t3)
              (match-literal
                t3 S '()
                (lambda (v^)
                  (let ([S^ (simple-ext-s-no-check v^ '() S)])
                    (body b c S^)))
                (lambda ()
                  (body b c S))))))))))

(define (ex1-macros-direct-always-alloc a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)]
         [b (var sc)]
         [c (var sc)])
    (let ([body (lambda (b c S^) S^)])
          (mmatch-pair a S
            [v^
             (body b c (simple-ext-s-no-check v^ (list b c) S))]
            [(b t2)
             (mmatch-pair t2 S
               [v^ (body b c (simple-ext-s-no-check v^ (list c) S))]
               [(c t3)
                (mmatch-lit t3 S '()
                  [v^ (body b c (simple-ext-s-no-check v^ '() S))]
                  [(body b c S)])])]))))

(define (ex1-functions-direct-always-alloc a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)]
         [b (var sc)]
         [c (var sc)])
    (let* ([body (lambda (b c S^) S^)])
      (match-pair
        a S
        (lambda (v^)
          (body b c (simple-ext-s-no-check v^ (list b c) S)))
        (lambda (b t2)
          (match-pair
            t2 S
            (lambda (v^)
              (body b c (simple-ext-s-no-check v^ (list c) S)))
            (lambda (c t3)
              (match-literal-no-check
                t3 S '()
                (lambda (v^)
                  (body b c (simple-ext-s-no-check v^ '() S)))
                (lambda ()
                  (body b c S))))))))))

(define (ex1-macros-direct-always-ext a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)]
         [b (var sc)]
         [c (var sc)])
    (let ([body (lambda (S^) S^)])
          (mmatch-pair a S
            [v^
             (body (simple-ext-s-no-check v^ (list b c) S))]
            [(b-v t2)
             (let ([S (simple-ext-s-no-check b b-v S)])
               (mmatch-pair t2 S
                 [v^ (body (simple-ext-s-no-check v^ (list c) S))]
                 [(c-v t3)
                  (let ([S (simple-ext-s-no-check c c-v S)])
                    (mmatch-lit t3 S '()
                      [v^ (body (simple-ext-s-no-check v^ '() S))]
                      [(body S)]))]))]))))

;;;
;;; ex1-combinators
;;;

; Lets try combinators with two cases: one for matching, one for constructing.

(define (c-pair s1-m s1-c s2-m s2-c)
  (let ([this-c (lambda ()
                  (cons (s1-c) (s2-c)))])
    (values
      (lambda (v S k)
        (let ([v^ (walk v S)])
          (cond
            [(var? v^) (k (simple-ext-s-no-check v^ (this-c) S))]
            [(pair? v^)
             (s1-m
               (car v^) S
               (lambda (S^)
                 (s2-m (cdr v^) S^ k)))]
            [else #f])))
      this-c)))

(define (c-literal lit)
  (values
    (lambda (v S k)
      (let ([v^ (walk v S)])
        (cond
          [(var? v^) (k (simple-ext-s-no-check v^ lit S))]
          [(equal? v^ lit)
           (k S)]
          [else #f])))
    (lambda ()
      lit)))

(define (c-var x)
  (values (lambda (v S k)
            (let ([v^ (walk v S)])
              (k (simple-ext-s-no-check x v S))))
          (lambda ()
            x)))

(define (ex1-combinators a st)
  (let* ([S (state-S st)]
         [sc (subst-scope S)]
         [b (var sc)]
         [c (var sc)])
    (let ([body (lambda (S^) S^)])
      (let*-values ([(v1-m v1-c) (c-var b)]
                    [(v2-m v2-c) (c-var c)]
                    [(l1-m l1-c) (c-literal '())]
                    [(p2-m p2-c) (c-pair v2-m v2-c l1-m l1-c)]
                    [(p1-m p1-c) (c-pair v1-m v1-c p2-m p2-c)])
        (p1-m a S body)))))

(define-syntax test-ex1-variants
  (syntax-rules ()
    [(_ descr (call arg ...))
     (time-test-variants descr
       ; variants of example 1 to test
       (ex1-unify
        ex1-manual-continuations
        ex1-manual-direct
        ex1-macros-direct
        ex1-functions-direct
        ex1-macros-direct-always-alloc
        ex1-macros-direct-always-ext
        ex1-combinators)
       (call arg ...))]))

; ground argument
(let ([st empty-state]
      [a '(1 2)])
  (test-ex1-variants "ex1 ground argument"
    (call a st)))

(let* ([st empty-state]
       [a (var (subst-scope (state-S st)))]
       [st (state-with-scope st (new-scope))])
  (test-ex1-variants "ex1 fresh argument"
    (call a st)))

(let* ([st empty-state]
       [a (cons (var (subst-scope (state-S st))) '(2))]
       [st (state-with-scope st (new-scope))])
  (test-ex1-variants "ex1 partially ground: `(,v 2)"
    (call a st)))

(let* ([st empty-state]
       [a (cons 1 (var (subst-scope (state-S st))))]
       [st (state-with-scope st (new-scope))])
  (test-ex1-variants "ex1 partially ground: `(1 . v)"
    (call a st)))

(let* ([st empty-state]
       [a (cons 1 (cons 2 (var (subst-scope (state-S st)))))]
       [st (state-with-scope st (new-scope))])
  (test-ex1-variants "ex1 partially ground: `(1 2 . v)"
    (call a st)))


; Notes on evaluation so far:
;
;  - runtime combinator composition is indeed slow
;  - always allocating variables isn't such a big deal... even if we always extend them
;      we can get a 3x boost from specialization. So we could have a nice compositional compilation
;      strategy that way.
;  - avoiding extending the substitution definitely makes compilation trickier, but it's fastest.
