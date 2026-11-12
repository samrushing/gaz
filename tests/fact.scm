;; -*- mode: gaz -*-

;; a loop with two accumulators: `let loop` and `goto`.

(define (fact:i64 n:i64)
  (let loop ((n:i64 n)
             (a:i64 1))
    (if (> n 1)
        (goto loop (- n 1) (* n a))
        a)))

(define (main:i64)
  (print (fact 5))
  (print (fact 20))
  0)
