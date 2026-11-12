;; -*- mode: gaz -*-

;; a 64x64 -> 128 multiply via zext and trunc, and 8-bit wraparound.

(define (mulhi:i64 a:i64 b:i64)
  (let ((m:i128 (* (zext i128 a) (zext i128 b))))
    (trunc i64 (>> m 64))))

(define (mullo:i64 a:i64 b:i64)
  (* a b))

(define (main:i32)
  (print (mulhi #xfedcba9876543210 #x0123456789abcdef))
  (print (mullo #xfedcba9876543210 #x0123456789abcdef))
  (let ((x:i8 250))
    (print (+ x 10)))
  0)
