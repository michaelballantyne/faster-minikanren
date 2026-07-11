#lang racket

(require "main.rkt")

(include "numbers.scm")

; The generic Chapter 2/4 list helpers and the bit relations are
; implementation details of the arithmetic system; don't export them,
; both to keep the public interface small and to avoid clashing with
; the common names nullo/conso/caro/cdro.
(provide (except-out (all-defined-out)
                     appendo
                     nullo conso caro cdro
                     bit-xoro bit-ando))
