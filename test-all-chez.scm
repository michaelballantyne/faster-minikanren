; Chez Scheme test runner. Loads the library and all tests, then exits
; with a non-zero status if any test failed (so CI can detect failures).
(load "mk-vicare.scm")
(load "mk.scm")
(load "test-all.scm")
(exit (if test-failed 1 0))
