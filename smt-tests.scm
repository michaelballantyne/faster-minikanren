(load "mk-vicare.scm")
(load "mk.scm")
(load "match.scm")
(load "smt.scm")
(load "../clpsmt-miniKanren/test-check.scm")

;;(load "../clpsmt-miniKanren/z3-driver.scm")
;;(load "../clpsmt-miniKanren/cvc4-driver.scm")
(load "../clpsmt-miniKanren/z3-server.scm")
;(load "../clpsmt-miniKanren/cvc4-server.scm")
;;(load "../clpsmt-miniKanren/cvc4-server-robust.scm")

;(set! log-all-calls #t)

;(mode 'naive)
;(mode `(assumptions 1000 #f))  ; don't assert negative assms. seems faster.
;(mode `(assumptions 1000 #t))  ; asssert negative assms
;(mode 'push-pop)
(mode 'reset-as-pop-push)

(load "../clpsmt-miniKanren/talk.scm")
(load "../clpsmt-miniKanren/radi-tests.scm")
(load "../clpsmt-miniKanren/radiw-concrete-tests.scm")
;;(load "../clpsmt-miniKanren/full-abstract-interp-extended-tests.scm")
(load "../clpsmt-miniKanren/rsa.scm")
(load "../clpsmt-miniKanren/property-based-synthesis-tests.scm")
;(load "../clpsmt-miniKanren/twenty-four-puzzle.scm")
(load "smt-extra-tests.scm")
(displayln (mode))
(exit)
