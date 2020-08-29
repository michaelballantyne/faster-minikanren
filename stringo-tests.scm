(test "stringo-1"
  (run* (q) (stringo q))
  '((_.0 (str _.0))))

(test "stringo-2"
  (run* (q) (stringo q) (== "x" q))
  '("x"))

(test "stringo-3"
  (run* (q) (== "x" q) (stringo q))
  '("x"))

(test "stringo-4"
  (run* (q) (== 5 q) (stringo q))
  '())

(test "stringo-5"
  (run* (q) (stringo q) (== 5 q))
  '())

(test "stringo-6"
  (run* (q) (stringo q) (== `(1 . 2) q))
  '())

(test "stringo-7"
  (run* (q) (== `(1 . 2) q) (stringo q))
  '())

(test "stringo-8"
  (run* (q) (fresh (x) (stringo x)))
  '(_.0))

(test "stringo-9"
  (run* (q) (fresh (x) (stringo x)))
  '(_.0))

(test "stringo-10"
  (run* (q) (fresh (x) (stringo x) (== x q)))
  '((_.0 (str _.0))))

(test "stringo-11"
  (run* (q) (fresh (x) (stringo q) (== x q) (stringo x)))
  '((_.0 (str _.0))))

(test "stringo-12"
  (run* (q) (fresh (x) (stringo q) (stringo x) (== x q)))
  '((_.0 (str _.0))))

(test "stringo-13"
  (run* (q) (fresh (x) (== x q) (stringo q) (stringo x)))
  '((_.0 (str _.0))))

(test "stringo-14-a"
  (run* (q) (fresh (x) (stringo q) (== "y" x)))
  '((_.0 (str _.0))))

(test "stringo-14-b"
  (run* (q) (fresh (x) (stringo q) (== "y" x) (== x q)))
  '("y"))

(test "stringo-15"
  (run* (q) (fresh (x) (== q x) (stringo q) (== 5 x)))
  '())

(test "stringo-16-a"
  (run* (q) (stringo q) (=/= 5 q))
  '((_.0 (str _.0))))

(test "stringo-16-b"
  (run* (q) (=/= 5 q) (stringo q))
  '((_.0 (str _.0))))

(test "stringo-17"
  (run* (q) (stringo q) (=/= `(1 . 2) q))
  '((_.0 (str _.0))))

(test "stringo-18"
  (run* (q) (stringo q) (=/= "y" q))
  '((_.0 (=/= ((_.0 "y"))) (str _.0))))

(test "stringo-19"
  (run* (q)
    (fresh (x y)
      (stringo x)
      (stringo y)
      (== `(,x ,y) q)))
  '(((_.0 _.1) (str _.0 _.1))))

(test "stringo-20"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (stringo x)
      (stringo y)))
  '(((_.0 _.1) (str _.0 _.1))))

(test "stringo-21"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (stringo x)
      (stringo x)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-22"
  (run* (q)
    (fresh (x y)
      (stringo x)
      (stringo x)
      (== `(,x ,y) q)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-23"
  (run* (q)
    (fresh (x y)
      (stringo x)
      (== `(,x ,y) q)
      (stringo x)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-24-a"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w . ,x) `(,y . ,z))
      (stringo w)
      (stringo z)))
  '(_.0))

(test "stringo-24-b"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w . ,x) `(,y . ,z))
      (stringo w)
      (stringo z)
      (== `(,w ,x ,y ,z) q)))
  '(((_.0 _.1 _.2 _.3)
     (=/= ((_.0 _.2) (_.1 _.3)))
     (str _.0 _.3))))

(test "stringo-24-c"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w . ,x) `(,y . ,z))
      (stringo w)
      (stringo y)
      (== `(,w ,x ,y ,z) q)))
  '(((_.0 _.1 _.2 _.3)
     (=/= ((_.0 _.2) (_.1 _.3)))
     (str _.0 _.2))))

(test "stringo-24-d"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w . ,x) `(,y . ,z))
      (stringo w)
      (stringo y)
      (== w y)
      (== `(,w ,x ,y ,z) q)))
  '(((_.0 _.1 _.0 _.2)
     (=/= ((_.1 _.2)))
     (str _.0))))

(test "stringo-25"
  (run* (q)
    (fresh (w x)
      (=/= `(,w . ,x) `(5 . 6))
      (== `(,w ,x) q)))
  '(((_.0 _.1) (=/= ((_.0 5) (_.1 6))))))

(test "stringo-26"
  (run* (q)
    (fresh (w x)
      (=/= `(,w . ,x) `(5 . 6))
      (stringo w)
      (== `(,w ,x) q)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-27"
  (run* (q)
    (fresh (w x)
      (stringo w)
      (=/= `(,w . ,x) `(5 . 6))
      (== `(,w ,x) q)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-28"
  (run* (q)
    (fresh (w x)
      (stringo w)
      (=/= `(5 . 6) `(,w . ,x))
      (== `(,w ,x) q)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-29"
  (run* (q)
    (fresh (w x)
      (stringo w)
      (=/= `(5 . ,x) `(,w . 6))
      (== `(,w ,x) q)))
  '(((_.0 _.1) (str _.0))))

(test "stringo-30"
  (run* (q)
    (fresh (w x)
      (stringo w)
      (=/= `("z" . ,x) `(,w . 6))
      (== `(,w ,x) q)))
  '(((_.0 _.1) (=/= ((_.0 "z") (_.1 6))) (str _.0))))

(test "stringo-31-a"
  (run* (q)
    (fresh (w x y z)
      (== x 5)
      (=/= `(,w ,y) `(,x ,z))
      (== w 5)
      (== `(,w ,x ,y ,z) q)))
  '(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-31-b"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w ,y) `(,x ,z))
      (== w 5)
      (== x 5)
      (== `(,w ,x ,y ,z) q)))
  '(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-31-c"
  (run* (q)
    (fresh (w x y z)
      (== w 5)
      (=/= `(,w ,y) `(,x ,z))
      (== `(,w ,x ,y ,z) q)
      (== x 5)))
  '(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-31-d"
  (run* (q)
    (fresh (w x y z)
      (== w 5)
      (== x 5)
      (=/= `(,w ,y) `(,x ,z))
      (== `(,w ,x ,y ,z) q)))
  '(((5 5 _.0 _.1) (=/= ((_.0 _.1))))))


(test "stringo-32-a"
  (run* (q)
    (fresh (w x y z)
      (== x 'a)
      (=/= `(,w ,y) `(,x ,z))
      (== w 'a)
      (== `(,w ,x ,y ,z) q)))
  '(((a a _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-32-b"
  (run* (q)
    (fresh (w x y z)
      (=/= `(,w ,y) `(,x ,z))
      (== w 'a)
      (== x 'a)
      (== `(,w ,x ,y ,z) q)))
  '(((a a _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-32-c"
  (run* (q)
    (fresh (w x y z)
      (== w 'a)
      (=/= `(,w ,y) `(,x ,z))
      (== `(,w ,x ,y ,z) q)
      (== x 'a)))
  '(((a a _.0 _.1) (=/= ((_.0 _.1))))))

(test "stringo-32-d"
  (run* (q)
    (fresh (w x y z)
      (== w 'a)
      (== x 'a)
      (=/= `(,w ,y) `(,x ,z))
      (== `(,w ,x ,y ,z) q)))
  '(((a a _.0 _.1) (=/= ((_.0 _.1))))))

(test "string-diseq-ordering"
  (run* (q)
    (=/= q "!")
    (=/= q '!))
  '((_.0 (=/= ((_.0 "!")) ((_.0 !))))))

(test "string-diseq-ordering"
  (run* (q)
    (=/= q 'a)
    (=/= q "a"))
  '((_.0 (=/= ((_.0 "a")) ((_.0 a))))))
