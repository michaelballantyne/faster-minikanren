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

(require (rename-in "private-unstable.rkt"
                    [fail mk:fail]
                    [succeed mk:succeed]))

(define fail (procedure-rename mk:fail 'fail))
(define succeed (procedure-rename mk:succeed 'succeed))
