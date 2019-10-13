(load "mk-vicare.scm")
(load "mk.scm")
(load "smt.scm")
(load "../clpsmt-miniKanren/test-check.scm")

;;(load "../clpsmt-miniKanren/z3-driver.scm")
;;(load "../clpsmt-miniKanren/cvc4-driver.scm")
(load "../clpsmt-miniKanren/z3-server.scm")
(load "../clpsmt-miniKanren/talk.scm")
(load "../clpsmt-miniKanren/radi-tests.scm")
(load "../clpsmt-miniKanren/radiw-concrete-tests.scm")
;;(load "../clpsmt-miniKanren/full-abstract-interp-extended-tests.scm")
(load "../clpsmt-miniKanren/rsa.scm")
(load "../clpsmt-miniKanren/property-based-synthesis-tests.scm")
;;slow
;;(load "../clpsmt-miniKanren/twenty-four-puzzle.scm")

(test "conde"
  (run 3 (q)
    (conde
      ((z/assert `(= ,q 1)))
      ((z/assert `(= ,q 2)))))
  '(1 2))

(test "faco-0"
  (run* (q)
    (fresh (out)
      (faco 0 out)
      (== q out)))
  '(1))

(test "faco-1"
  (run 1 (q)
    (fresh (out)
      (faco 1 out)
      (== q out)))
  '(1))

(run 3 (q)
  (fresh (n out)
    (facto n out)
    (== q `(,n ,out))))
