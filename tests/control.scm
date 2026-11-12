;; -*- mode: gaz -*-

;; control flow: cond, when, while, n-ary comparison, and/or.

(define (classify:i32 n:i32)
  (cond ((> n 3) 34)
        ((> n 2) 19)
        (else 7)))

(define (between:i32 lo:i32 x:i32 hi:i32)
  (if (< lo x hi) 1 0))

;; sum of the odd numbers below n.
(define (sum-odd:i32 n:i32)
  (let loop ((i:i32 0)
             (sum:i32 0))
    (if (< i n)
        (goto loop (+ i 1) (if (= 1 (& i 1)) (+ sum i) sum))
        sum)))

(define (main:i32)
  (print (classify 4))
  (print (classify 3))
  (print (classify 0))
  (print (between 1 5 9))
  (print (between 1 9 5))
  (print (sum-odd 10))
  0)
