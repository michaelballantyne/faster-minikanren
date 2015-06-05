(define empty-subst '())

(define subst-length length)

; Returns #f if not found, or a pair of u and the result of the lookup.
; This distinguishes between #f indicating absence and being the result.
(define subst-lookup assq)

(define (subst-add S var val)
  (cons (cons var val) S))

(define subst-eq? eq?)
