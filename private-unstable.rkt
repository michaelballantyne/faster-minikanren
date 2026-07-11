#lang racket/base

(provide (all-defined-out))

(require racket/list
         racket/include)

;; extra stuff for racket
;; due mostly to samth
(module compatibility racket/base
  (provide (all-defined-out))

  (define (list-sort f l) (sort l f))

  (define (exists f l) (ormap f l))

  (define format-error error))

(require (submod "." compatibility))

(define empty-intmap (hasheq))
(define (intmap-count m) (hash-count m))
(define (intmap-ref m k) (hash-ref m k (lambda () unbound)))
(define (intmap-set m k v) (hash-set m k v))

(include "mk.scm")
