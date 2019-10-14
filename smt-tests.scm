(load "mk-vicare.scm")
(load "mk.scm")
(load "smt.scm")
(load "../clpsmt-miniKanren/test-check.scm")

;;(load "../clpsmt-miniKanren/z3-driver.scm")
;;(load "../clpsmt-miniKanren/cvc4-driver.scm")
(load "../clpsmt-miniKanren/z3-server.scm")
;;(load "../clpsmt-miniKanren/cvc4-server.scm")
(load "../clpsmt-miniKanren/talk.scm")
(load "../clpsmt-miniKanren/radi-tests.scm")
(load "../clpsmt-miniKanren/radiw-concrete-tests.scm")
;;(load "../clpsmt-miniKanren/full-abstract-interp-extended-tests.scm")
(load "../clpsmt-miniKanren/rsa.scm")
(load "../clpsmt-miniKanren/property-based-synthesis-tests.scm")
;;(load "../clpsmt-miniKanren/mk.scm")
;;(load "../clpsmt-miniKanren/z3-driver.scm")
;;slow
;;(load "../clpsmt-miniKanren/twenty-four-puzzle.scm")

(test "conde"
  (run 3 (q)
    (conde
      ((z/assert `(= ,q 1)))
      ((z/assert `(= ,q 2)))))
  '(1 2))

(test "join"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (conde
        ((== a 4))
        ((== a 2)))
      (z/assert `(= ,a (+ ,b ,b)))))
  '((4 2) (2 1)))

(test "unif"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (z/assert `(> ,a 0))
      (== b 2)
      (== b a)))
  '((2 2)))

(test "unif2"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (z/assert `(> ,a 0))
      (== b a)
      (== b 2)))
  '((2 2)))

(test "faco-0"
  (run* (q)
    (fresh (out)
      (faco 0 out)
      (== q out)))
  '(1))

(test "faco-1"
  (run* (q)
    (fresh (out)
      (faco 1 out)
      (== q out)))
  '(1))

(run 7 (q)
  (fresh (n out)
    (faco n out)
    (== q `(,n ,out))))

(run 7 (q)
  (fresh (n out)
    (facto n out)
    (== q `(,n ,out))))

(test "evalo-backwards-fib-quoted-6"
  (run 1 (q)
    (evalo `(letrec ((f
                      (lambda (n)
                        (if (< n 0) #f
                            (if (< n 2) n
                                (+ (f (- n 1)) (f (- n 2))))))))
              (f ',q))
           8))
  '(6))

(test "fail-1"
  (run 1 (x)
    (=/= x 2)
    (z/assert `(> ,x 1))
    (z/assert `(< ,x 3)))
  '())

(test "fail-2"
  (run 1 (x)
    (absento 2 x)
    (z/assert `(> ,x 1))
    (z/assert `(< ,x 3)))
  '())
