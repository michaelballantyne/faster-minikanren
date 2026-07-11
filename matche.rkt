#lang racket
(require "mk.rkt")
(require (for-syntax racket/syntax))

(provide matche lambdae defmatche)

(define-for-syntax memp memf)
(define-for-syntax format-error error)

(include "matche.scm")
