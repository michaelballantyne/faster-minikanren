#lang racket/base

(provide run run* defrel
         fail succeed
         == =/=
         fresh
         conde
         symbolo numbero stringo
         absento
         project
         var?
         always-wrap-reified?)

(require "private-unstable.rkt"
         (prefix-in mk: "private-unstable.rkt"))

(define fail (procedure-rename mk:fail 'fail))
(define succeed (procedure-rename mk:succeed 'succeed))
