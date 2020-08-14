#lang racket/base

(require racket/list
         racket/include)

(provide run run*
         == =/=
         fresh
         conde
         symbolo numbero stringo
         absento
         project
         var?
         always-wrap-reified?)

(define empty-intmap (hasheq))
(define (intmap-count m) (hash-count m))
(define (intmap-ref m k) (hash-ref m k (lambda () unbound)))
(define (intmap-set m k v) (hash-set m k v))

;; extra stuff for racket
;; due mostly to samth
(define (list-sort f l) (sort l f))

(define (remp f l) (filter-not f l))

(define (call-with-string-output-port f)
  (define p (open-output-string))
  (f p)
  (get-output-string p))

(define (exists f l) (ormap f l))

(define for-all andmap)

(define (find f l)
  (cond [(memf f l) => car] [else #f]))

(define memp memf)

(define (var*? v) (var? (car v)))

(include "mk.scm")
