(define-module (faster-minikanren mk-guile)
  #:export (run run* defrel
            == =/=
            fresh
            conde
            symbolo numbero stringo
            absento
            succeed fail
            matche))

(import (rnrs (6)))
(import (rnrs records syntactic (6)))

(define fxsra fxarithmetic-shift-right)
(define fxsll bitwise-arithmetic-shift-left)

(include-from-path "faster-minikanren/mk-vicare.scm")
(include-from-path "faster-minikanren/mk.scm")

(define andmap and-map)
(define ormap or-map)

(define generate-temporary gensym)

(include-from-path "faster-minikanren/matche.scm")
