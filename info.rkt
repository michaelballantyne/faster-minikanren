#lang info

(define collection "minikanren")
(define version "1.0")
(define deps '("base"))

(define compile-omit-paths 'all)
(define compile-include-files
  '("main.rkt"
    "numbers.rkt"
    "matche.rkt"
    "simple-interp.rkt"
    "full-interp.rkt"))

(define test-omit-paths '(#rx".*[.](scm)"))
(define test-include-paths '("test-all.rktl"))
