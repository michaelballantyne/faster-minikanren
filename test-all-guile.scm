; Guile test runner. Loads the library module and all tests, then exits
; with a non-zero status if any test failed (so CI can detect failures).
(use-modules (faster-minikanren mk-guile))

(define (printf . args)
  (apply format #t args))

(load "test-all.scm")
(exit (if test-failed 1 0))
