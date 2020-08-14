; This file needs to be loaded before mk.scm for Vicare. I can't figure
; out how to do loads relative to a source file rather than the working
; directory, else this file would load mk.scm.

; Trie implementation. The initial original trie version was due to Abdulaziz Ghuloum.
; Greg Rosenblatt changed it to an N-way Trie to reduce depth.

;;; subst ::= (empty)
;;;         | (node even odd)
;;;         | (data idx val)

(define-record-type node (fields e o))
(define-record-type data (fields idx val))

(define shift (lambda (n) (fxsra n 1)))
(define unshift (lambda (n i) (fx+ (fxsll n 1) i)))

(define shift-size 4)
(define node-size (fxsll 1 shift-size))
(define local-mask (fx- node-size 1))
(define (shift-n xi) (fxsra xi shift-size))
(define (local-n xi) (fxand xi local-mask))
(define node-n? vector?)
(define (node-n-new i0 v0)
  (define result (make-vector (fx+ i0 1) '()))
  (vector-set! result i0 v0)
  result)
(define (node-n-get nd idx)
  (if (fx<? idx (vector-length nd)) (vector-ref nd idx) '()))
(define (node-n-put nd idx val)
  (define len0 (vector-length nd))
  (define len1 (fxmax len0 (fx+ idx 1)))
  (define result (make-vector len1 '()))
  (let copy ((ci 0))
    (if (fx=? len0 ci) (begin (vector-set! result idx val) result)
      (begin (vector-set! result ci (vector-ref nd ci)) (copy (fx+ ci 1))))))

(define (nwt:size trie)
  (cond
    ((node-n? trie)
     (let loop ((ci 0) (sz 0))
       (if (fx=? node-size ci) sz
         (loop (fx+ ci 1) (fx+ sz (nwt:size (node-n-get trie ci)))))))
    ((data? trie) 1)
    (else 0)))

(define (nwt:lookup trie xi)
  (cond
    ((node-n? trie) (nwt:lookup (node-n-get trie (local-n xi)) (shift-n xi)))
    ((data? trie) (and (fx=? xi (data-idx trie)) trie))
    (else #f)))

(define (nwt:bind trie xi val)
  (cond
    ((node-n? trie)
     (let ((li (local-n xi)))
       (node-n-put trie li (nwt:bind (node-n-get trie li) (shift-n xi) val))))
    ((data? trie)
     (let ((xi0 (data-idx trie)))
       (if (fx=? xi0 xi) (make-data xi val)
         (nwt:bind (node-n-new (local-n xi0) (make-data (shift-n xi0) (data-val trie)))
                   xi val))))
    (else (make-data xi val))))


(define t:size nwt:size)

(define t:bind
  (lambda (xi v s)
    (unless (and (fixnum? xi) (>= xi 0))
      (error 't:bind "index must be a fixnum, got ~s" xi))
    (nwt:bind s xi v)))

(define t:lookup
  (lambda (xi s)
    (unless (and (fixnum? xi) (>= xi 0))
      (error 't:lookup "index must be a fixnum, got ~s" xi))
    (nwt:lookup s xi)))


; intmap

(define empty-intmap '())
(define (intmap-count m) (t:size m))
(define (intmap-ref m k)
  (let ([res (t:lookup k m)])
    (if res
      (data-val res)
      unbound)))
(define (intmap-set m k v) (t:bind k v m))


; Misc. missing functions

(define (remove-duplicates l)
  (cond ((null? l)
         '())
        ((member (car l) (cdr l))
         (remove-duplicates (cdr l)))
        (else
         (cons (car l) (remove-duplicates (cdr l))))))

(define (foldl f init seq)
  (if (null? seq)
    init
    (foldl f
           (f (car seq) init)
           (cdr seq))))

(define (filter-map f l) (filter (lambda (x) x) (map f l)))

(define (append* l*) (apply append l*))
