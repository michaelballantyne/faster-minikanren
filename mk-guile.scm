(define-module (faster-miniKanren mk-guile)
  #:export (run run*
            == =/=
            fresh
            conde
            symbolo numbero
            absento
            matche))

(import (rnrs (6)))
(import (rnrs records syntactic (6)))

(define sub1 1-)
(define add1 1+)

(define fx= fx=?)
(define fxsla fxarithmetic-shift-left)
(define fxsra fxarithmetic-shift-right)
(define fxsll bitwise-arithmetic-shift-left)

(include-from-path "faster-miniKanren/mk-vicare.scm")
(include-from-path "faster-miniKanren/mk.scm")

(define (andmap proc . args)
  (let ((l (length (car args))))
    (when (pair? (filter (lambda (x) (not (= l (length x)))) args))
      (error 'andmap "Lists of unequal length" args)))
  (let rec
    ((result '())
     (args args))
    (if (equal? (car args) '())
      (reverse result)
      (let ((val (apply proc (map car args))))
        (if (not val)
          (reverse result)
          (rec (cons val result)
               (map cdr args)))))))

(define generate-temporary gensym)

(include-from-path "faster-miniKanren/matche.scm")
