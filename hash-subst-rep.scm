(define empty-subst-map (hasheq))

(define subst-map-length hash-count)

; Returns #f if not found, or a pair of u and the result of the lookup.
; This distinguishes between #f indicating absence and being the result.
(define subst-map-lookup
  (lambda (u S)
    (hash-ref S u unbound)))

(define (subst-map-add S var val)
  (hash-set S var val))

(define subst-map-eq? eq?)
