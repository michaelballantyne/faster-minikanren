(define partition
  (lambda (p xs)
    (cons (filter p xs)
          (filter (lambda (x) (not (p x))) xs))))

(define declare-datatypes?
  (lambda (s)
    (and (pair? s)
         (or (eq? 'declare-datatypes (car s))
             (eq? 'declare-sort (car s)))
         (cadr s))))

(define declares?
  (lambda (s)
    (and (pair? s)
         (or (eq? 'declare-fun (car s))
             (eq? 'declare-const (car s)))
         (cadr s))))

(define filter-redundant-declare
  (lambda (d es)
    (filter
     (lambda (e)
       (or (not (eq? (cadr e) (cadr d)))
           (if (equal? e d) #f
               (error 'filter-redundant-declare "inconsistent" d e))))
     es)))

(define filter-redundant-declares
  (lambda (ds es)
    (if (null? ds)
        es
        (filter-redundant-declares
         (cdr ds)
         (cons (car ds) (filter-redundant-declare (car ds) es))))))

(define decls '())
(define undeclared?
  (lambda (ds) (if (null? ds) (lambda (x) #t) (lambda (x) (and (not (memq x ds)) (not (memq x decls)))))))

(define (range a b)
  (if (>= a b) '() (cons a (range (1+ a) b))))

(define map-to-list
  (lambda (S) S))

(define (is-reified-var? x)
  (and (symbol? x)
       (let ((s (symbol->string x)))
         (and (> (string-length s) 2)
              (eq? (string-ref s 0) #\_)
              (eq? (string-ref s 1) #\.)))))

(define m-subst-map empty-subst-map)
(define z/reify-SM
  (lambda (M)
    (lambda (st)
      (let* ((S (state-S st))
             (M (walk* (reverse M) S))
             (S (reify-S M (subst
                            ;; (map (lambda (x)
                            ;;        (if (not (is-reified-var? (walk (walk (car x) S) (subst m-subst-map nonlocal-scope)))) (cons (var nonlocal-scope) (cdr x)) x))
                                 m-subst-map
                                 ;;)
                            nonlocal-scope)))
             (_ (set! m-subst-map (filter (lambda (x) (is-reified-var? (cdr x))) (subst-map S))))
             (M (walk* M S))
             (dd-M (partition declare-datatypes? M))
             (dd (car dd-M))
             (M (cdr dd-M))
             (ds-R (partition declares? M))
             (ds (car ds-R))
             (R (cdr ds-R))
             (ds (filter-redundant-declares ds ds))
             (M (append ds R))
             (S (map-to-list (subst-map S)))
             (_ (set! decls (append (map cadr ds) decls)))
             (dc (map (lambda (x)
                        (set! decls (cons x decls))
                        `(declare-fun ,x () Int))
                      (filter (undeclared? decls) (map cdr S)))))
        (cons
         (map (lambda (x) (cons (cdr x) (car x))) S)
         (append
          dd
          dc
          M))))))

(define (check-sat-assuming a xs)
  (call-z3 `(,@xs (check-sat-assuming (,a))))
  (read-sat))

(define (take-until p xs)
  (if (null? xs)
      '()
      (if (p (car xs))
          (cons (car xs) '())
          (cons (car xs) (take-until p (cdr xs))))))

(define (z/check a)
  (lambdag@ (st)
    (if (check-sat-assuming a (cdr ((z/reify-SM (take-until (lambda (x) (equal? x `(declare-const ,a Bool)))
                                                            (state-M st))) st)))
        st
        #f)))

(define z/
  (lambda (line)
    (lambdag@ (st)
      (let ((M (cons line (state-M st))))
        (state (state-S st) (state-C st) M)))))

(define assumption-count 0)
(define (fresh-assumption)
  (set! assumption-count (+ assumption-count 1))
  (string->symbol (format #f "a~d" assumption-count)))

(define (last-assumption m)
  (let ((r (filter (lambda (x) (and (pair? x)
                               (eq? 'assert (car x))
                               (pair? (cadr x))
                               (eq? (car (cadr x)) '=>)))
                   m)))
    (if (null? r)
        'true
        (cadr (cadr (car r))))))

(define z/assert
  (lambda (e)
    (lambdag@ (st)
      (let ((a1 (fresh-assumption))
            (a2 (fresh-assumption)))
        (let ((a0 (last-assumption (state-M st))))
          ((fresh ()
             (z/ `(declare-const ,a2 Bool))
             (z/ `(declare-const ,a1 Bool))
             (z/ `(assert (=> ,a1 ,e)))
             (z/ `(assert (=> ,a2 (and ,a0 ,a1))))
             (z/check a2))
           st))))))

(define (z/reset!)
  (call-z3 '((reset)))
  (set! decls '())
  (set! assumption-count 0)
  (set! m-subst-map empty-subst-map))

(define add-model
  (lambda (m s)
    (lambdag@ (st)
      (if (null? m)
          st
          (bind
           (let ((b (assq (caar m) s)))
             (if b
                 ((== (cdr b) (cdar m)) st)
                 st))
           (add-model (cdr m) s))))))

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
          (let ([a (last-assumption (state-M st))]
                [SM ((z/reify-SM M) st)])
            (if (not (check-sat-assuming a '()))
                #f
                (if (null? (car SM))
                    (state (state-S st) (state-C st) '())
                    ((let loop ()
                        (lambdag@ (st)
                          (let ((m (get-model-inc)))
                            ((conde
                                ((add-model m (car SM)))
                                ((assert-neg-model m)
                                 (loop)))
                             st))))
                     st))))))))
