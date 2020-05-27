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

(test "unif-0"
  (run 1 (q)
    (fresh (x y)
      (== x y)
      (z/assert `(= ,x 1))
      (== y 2)))
  '())

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

(load "../clpsmt-miniKanren/full-interp-with-let.scm")
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

(test "fail-3"
  (run 2 (x)
    (=/= x 2)
    (z/assert `(= 4 (* ,x ,x))))
  '(-2))

(test "real-1"
  (run 1 (x)
    (z/ `(declare-const ,x Real))
    (z/assert `(= 4.2 (* 2 ,x))))
  '(2.1))

(test "diseq-0"
  (run 1 (q)
    (fresh (x y)
      (z/assert `(> ,x 0))
      (z/assert `(> ,y 0))
      (z/assert `(= ,q (* ,x ,y)))))
  '(1))

(test "diseq-1"
  (run 1 (q)
    (fresh (x y)
      (=/= x 0)
      (=/= y 0)
      (z/assert `(>= ,x 0))
      (z/assert `(>= ,y 0))
      (z/assert `(= ,q (* ,x ,y)))))
  '(1))


(test "diseq-2"
  (run 1 (q)
    (fresh (x y)
      (z/assert `(>= ,x 0))
      (z/assert `(>= ,y 0))
      (z/assert `(= ,q (* ,x ,y)))
      (=/= x 0)
      (=/= y 0)))
  '(1))

(test "diseq-3"
  (run 1 (q)
    (fresh (x y)
      (=/= x 0)
      (=/= y 0)
      (z/assert `(= 0 (* ,x ,y)))))
  '())

(test "diseq-4"
  (run 1 (q)
    (fresh (x y)
      (z/assert `(= 0 (* ,x ,y)))
      (=/= x 0)
      (=/= y 0)))
  '())

(test "unif-3"
      (run 2 (x y)
           (z/ `(assert (= ,x 1)))
           (== x y)
           (== y 2))
      '())

(test "decl"
      (run 2 (x)
           (z/ `(declare-const ,x Int)))
      '((_.0 (num _.0))))

(test "decl2"
      (run 2 (x)
           (z/ `(declare-const ,x Int))
           (symbolo x))
      '())

(test "decl3"
      (run 2 (x)
           (symbolo x)
           (z/ `(declare-const ,x Int)))
      '())


(test "type-1"
      (run 2 (x)
           (symbolo x)
           (z/assert `(= ,x ,x)))
      '())

(test "type-2"
      (run 2 (x)
           (z/assert `(= ,x ,x))
           (symbolo x))
      '())

(test "enum"
      (run 2 (x)
           (z/assert `(= ,x ,x)))
      '(0 1))


