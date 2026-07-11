;;; Copyright © 2018 Daniel P. Friedman, William E. Byrd, Oleg Kiselyov, and Jason Hemann
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


;;; Implementation of the arithmetic system used in 'The Reasoned
;;; Schemer, Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann
;;; (MIT Press, 2018).
;;;
;;; Adapted from
;;; https://github.com/TheReasonedSchemer2ndEd/CodeFromTheReasonedSchemer2ndEd/blob/master/trs2-arith.scm

;;; Definitions are presented in the order in which they appear in
;;; Chapters 7 and 8.

;;; As in the book, there are three definitions of '/o'.  The first two,
;;; flawed definitions, are commented out using Scheme's '#;' convention.
;;; The final definition of '/o' is uncommented.



; Helper definitions from Chapters 2 and 4.
(defrel (nullo x)
  (== '() x))

(defrel (conso a d p)
  (== `(,a . ,d) p))

(defrel (caro p a)
  (fresh (d)
    (== (cons a d) p)))

(defrel (cdro p d)
  (fresh (a)
    (== (cons a d) p)))

(defrel (appendo l t out)
  (conde
    ((nullo l) (== t out))
    ((fresh (a d res)
       (conso a d l)
       (conso a res out)
       (appendo d t res)))))



;;; Here are the key parts of Chapter 7
(defrel (bit-xoro x y r)
  (conde
    ((== 0 x) (== 0 y) (== 0 r))
    ((== 0 x) (== 1 y) (== 1 r))
    ((== 1 x) (== 0 y) (== 1 r))
    ((== 1 x) (== 1 y) (== 0 r))))

(defrel (bit-ando x y r)
  (conde
    ((== 0 x) (== 0 y) (== 0 r))
    ((== 1 x) (== 0 y) (== 0 r))
    ((== 0 x) (== 1 y) (== 0 r))
    ((== 1 x) (== 1 y) (== 1 r))))


(defrel (half-addero x y r c)
  (bit-xoro x y r)
  (bit-ando x y c))

; Alternative definition of 'half-addero' from frame 7:12 on page 87.
#;(defrel (half-addero x y r c)
  (conde
    ((== 0 x) (== 0 y) (== 0 r) (== 0 c))
    ((== 1 x) (== 0 y) (== 1 r) (== 0 c))
    ((== 0 x) (== 1 y) (== 1 r) (== 0 c))
    ((== 1 x) (== 1 y) (== 0 r) (== 1 c))))



; Definition of 'full-addero' from frame 7:15 on page 87.
#;(defrel (full-addero b x y r c)
  (fresh (w xy wz)
    (half-addero x y w xy)
    (half-addero w b r wz)
    (bit-xoro xy wz c)))

; Alternative definition of 'full-addero' from frame 7:15 on page 87.
;
; For performance reasons, we use this explicit table version of
; 'full-addero' (which no longer uses 'half-addero').
(defrel (full-addero b x y r c)
  (conde
    ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
    ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
    ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
    ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
    ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
    ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
    ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
    ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))


(define (build-num n)
  (cond
    ((zero? n) '())
    ((even? n)
     (cons 0
       (build-num (quotient n 2))))
    ((odd? n)
     (cons 1
       (build-num (quotient (- n 1) 2))))))

(defrel (zeroo n)
  (== '() n))

(defrel (poso n)
  (fresh (a d)
    (== `(,a . ,d) n)))

(defrel (>1o n)
  (fresh (a ad dd)
    (== `(,a ,ad . ,dd) n)))

(defrel (addero b n m r)
  (conde
    ((== 0 b) (== '() m) (== n r))
    ((== 0 b) (== '() n) (== m r)
     (poso m))
    ((== 1 b) (== '() m)
     (addero 0 n '(1) r))
    ((== 1 b) (== '() n) (poso m)
     (addero 0 '(1) m r))
    ((== '(1) n) (== '(1) m)
     (fresh (a c)
       (== `(,a ,c) r)
       (full-addero b 1 1 a c)))
    ((== '(1) n) (gen-addero b n m r))
    ((== '(1) m) (>1o n) (>1o r)
     (addero b '(1) n r))
    ((>1o n) (gen-addero b n m r))))

(defrel (gen-addero b n m r)
  (fresh (a c d e x y z)
    (== `(,a . ,x) n)
    (== `(,d . ,y) m) (poso y)
    (== `(,c . ,z) r) (poso z)
    (full-addero b a d c e)
    (addero e x y z)))

(defrel (pluso n m k)
  (addero 0 n m k))

(defrel (minuso n m k)
  (pluso m k n))

;;; Here are the key parts of Chapter 8
(defrel (*o n m p)
  (conde
    ((== '() n) (== '() p))
    ((poso n) (== '() m) (== '() p))
    ((== '(1) n) (poso m) (== m p))
    ((>1o n) (== '(1) m) (== n p))
    ((fresh (x z)
       (== `(0 . ,x) n) (poso x)
       (== `(0 . ,z) p) (poso z)
       (>1o m)
       (*o x m z)))
    ((fresh (x y)
       (== `(1 . ,x) n) (poso x)
       (== `(0 . ,y) m) (poso y)
       (*o m n p)))
    ((fresh (x y)
       (== `(1 . ,x) n) (poso x)
       (== `(1 . ,y) m) (poso y)
       (odd-*o x n m p)))))

(defrel (odd-*o x n m p)
  (fresh (q)
    (bound-*o q p n m)
    (*o x m q)
    (pluso `(0 . ,q) m p)))

(defrel (bound-*o q p n m)
  (conde
    ((== '() q) (poso p))
    ((fresh (a0 a1 a2 a3 x y z)
       (== `(,a0 . ,x) q)
       (== `(,a1 . ,y) p)
       (conde
         ((== '() n)
          (== `(,a2 . ,z) m)
          (bound-*o x y z '()))
         ((== `(,a3 . ,z) n)
          (bound-*o x y z m)))))))

(defrel (=lo n m)
  (conde
    ((== '() n) (== '() m))
    ((== '(1) n) (== '(1) m))
    ((fresh (a x b y)
       (== `(,a . ,x) n) (poso x)
       (== `(,b . ,y) m) (poso y)
       (=lo x y)))))

(defrel (<lo n m)
  (conde
    ((== '() n) (poso m))
    ((== '(1) n) (>1o m))
    ((fresh (a x b y)
       (== `(,a . ,x) n) (poso x)
       (== `(,b . ,y) m) (poso y)
       (<lo x y)))))

(defrel (<=lo n m)
  (conde
    ((=lo n m))
    ((<lo n m))))

(defrel (<o n m)
  (conde
    ((<lo n m))
    ((=lo n m)
     (fresh (x)
       (poso x)
       (pluso n x m)))))

(defrel (<=o n m)
  (conde
    ((== n m))
    ((<o n m))))

; Flawed definition of '/o' from frame 8:54 on page 118.
#;(defrel (/o n m q r)
  (conde
    ((== '() q) (== n r) (<o n m))
    ((== '(1) q) (== '() r) (== n m)
     (<o r m))
    ((<o m n) (<o r m)
     (fresh (mq)
       (<=lo mq n)
       (*o m q mq)
       (pluso mq r n)))))

; Flawed definition of '/o' from frame 8:64 on page 120.
#;(defrel (/o n m q r)
  (fresh (mq)
    (<o r m)
    (<=lo mq n)
    (*o m q mq)
    (pluso mq r n)))

(defrel (splito n r l h)
  (conde
    ((== '() n) (== '() h) (== '() l))
    ((fresh (b n^)
       (== `(0 ,b . ,n^) n) (== '() r)
       (== `(,b . ,n^) h) (== '() l)))
    ((fresh (n^)
       (==  `(1 . ,n^) n) (== '() r)
       (== n^ h) (== '(1) l)))
    ((fresh (b n^ a r^)
       (== `(0 ,b . ,n^) n)
       (== `(,a . ,r^) r) (== '() l)
       (splito `(,b . ,n^) r^ '() h)))
    ((fresh (n^ a r^)
       (== `(1 . ,n^) n)
       (== `(,a . ,r^) r) (== '(1) l)
       (splito n^ r^ '() h)))
    ((fresh (b n^ a r^ l^)
       (== `(,b . ,n^) n)
       (== `(,a . ,r^) r)
       (== `(,b . ,l^) l)
       (poso l^)
       (splito n^ r^ l^ h)))))

; Final definition of '/o' from frame 8:81 on page 124.
(defrel (/o n m q r)
  (conde
    ((== '() q) (== r n) (<o n m))
    ((== '(1) q) (=lo m n) (pluso r m n)
     (<o r m))
    ((poso q) (<lo m n) (<o r m)
     (n-wider-than-mo n m q r))))

(defrel (n-wider-than-mo n m q r)
  (fresh (nh nl qh ql)
    (fresh (mql mrql rr rh)
      (splito n r nl nh)
      (splito q r ql qh)
      (conde
        ((== '() nh)
         (== '() qh)
         (minuso nl r mql)
         (*o m ql mql))
        ((poso nh)
         (*o m ql mql)
         (pluso r mql mrql)
         (minuso mrql nl rr)
         (splito rr r '() rh)
         (/o nh m qh rh))))))

(defrel (logo n b q r)
  (conde
    ((== '() q) (<=o n b)
     (pluso r '(1) n))
    ((== '(1) q) (>1o b) (=lo n b)
     (pluso r b n))
    ((== '(1) b) (poso q)
     (pluso r '(1) n))
    ((== '() b) (poso q) (== r n))
    ((== '(0 1) b)
     (fresh (a ad dd)
       (poso dd)
       (== `(,a ,ad . ,dd) n)
       (exp2o n '() q)
       (fresh (s)
         (splito n dd r s))))
    ((<=o '(1 1) b) (<lo b n)
     (base-three-or-moreo n b q r))))

(defrel (exp2o n b q)
  (conde
    ((== '(1) n) (== '() q))
    ((>1o n) (== '(1) q)
     (fresh (s)
       (splito n b s '(1))))
    ((fresh (q1 b2)
       (== `(0 . ,q1) q) (poso q1)
       (<lo b n)
       (appendo b `(1 . ,b) b2)
       (exp2o n b2 q1)))
    ((fresh (q1 nh b2 s)
       (== `(1 . ,q1) q) (poso q1)
       (poso nh)
       (splito n b s nh)
       (appendo b `(1 . ,b) b2)
       (exp2o nh b2 q1)))))

(defrel (base-three-or-moreo n b q r)
  (fresh (bw1 bw nw nw1 ql1 ql s)
    (exp2o b '() bw1)
    (pluso bw1 '(1) bw)
    (<lo q n)
    (fresh (q1 bwq1)
      (pluso q '(1) q1)
      (*o bw q1 bwq1)
      (<o nw1 bwq1))
    (exp2o n '() nw1)
    (pluso nw1 '(1) nw)
    (/o nw bw ql1 s)
    (pluso ql '(1) ql1)
    (<=lo ql q)
    (fresh (bql qh s qdh qd)
      (repeated-mulo b ql bql)
      (/o nw bw1 qh s)
      (pluso ql qdh qh)
      (pluso ql qd q)
      (<=o qd qdh)
      (fresh (bqd bq1 bq)
        (repeated-mulo b qd bqd)
        (*o bql bqd bq)
        (*o b bq bq1)
        (pluso bq r n)
        (<o n bq1)))))

(defrel (repeated-mulo n q nq)
  (conde
    ((poso n) (== '() q) (== '(1) nq))
    ((== '(1) q) (== n nq))
    ((>1o q)
     (fresh (q1 nq1)
       (pluso q1 '(1) q)
       (repeated-mulo n q1 nq1)
       (*o nq1 n nq)))))

(defrel (expo b q n)
  (logo n b q '()))
