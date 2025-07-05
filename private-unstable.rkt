#lang racket/base

(provide (all-defined-out))

(require racket/list
         racket/include)

;; extra stuff for racket
;; due mostly to samth
(module compatibility racket/base
  (provide (all-defined-out))

  (require racket/list
		   (only-in racket/port
                    [call-with-output-string call-with-string-output-port]))

  (define (list-sort f l) (sort l f))

  (define remp filter-not)

  (define (exists f l) (ormap f l))

  (define for-all andmap)

  (define (find f l)
    (cond [(memf f l) => car] [else #f]))

  (define memp memf))

(require (submod "." compatibility))

(define empty-intmap (hasheq))
(define (intmap-count m) (hash-count m))
(define (intmap-ref m k) (hash-ref m k (lambda () unbound)))
(define (intmap-set m k v) (hash-set m k v))

(include "mk.scm")
