(define empty-subst-map '())

(define subst-map-length length)

; Returns #f if not found, or a pair of u and the result of the lookup.
; This distinguishes between #f indicating absence and being the result.
(define subst-map-lookup assq)

(define (subst-map-add S var val)
  (cons (cons var val) S))

(define subst-map-eq? eq?)
