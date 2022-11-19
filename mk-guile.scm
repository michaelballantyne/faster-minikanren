(define-module (faster-minikanren mk-guile)
  #:export (run run* defrel
            == =/=
            fresh
            conde
            symbolo numbero stringo
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

(include-from-path "faster-minikanren/mk-vicare.scm")
(include-from-path "faster-minikanren/mk.scm")

(define andmap and-map)
(define ormap or-map)

(define generate-temporary gensym)

(include-from-path "faster-minikanren/matche.scm")
