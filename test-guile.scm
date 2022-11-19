(use-modules (faster-minikanren mk-guile))

(define (printf . args)
  (apply format #t args))

(include "test-all.scm")
