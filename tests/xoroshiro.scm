;; -*- mode: gaz -*-

;; xoroshiro128+, with the 2018 constants (24, 16, 37).
;; http://vigna.di.unimi.it/xorshift/xoroshiro128plus.c

(define (xoroshiro128+:i64 s:(mut (vec 2 i64)))
  (let ((s0:i64 s[0])
        (s1:i64 s[1])
        (p:i64 (+ s0 s1))
        (x:i64 (xor s0 s1)))
    (set! s[0] (xor (<<< s0 24) x (<< x 16)))
    (set! s[1] (<<< x 37))
    p))

(define (main:i32)
  (let ((s:(mut (vec 2 i64)) (alloca)))
    (set! s[0] #x309812c06d126f64)
    (set! s[1] #x18562fcf1270f370)
    (for (i:i32 4)
      (print (xoroshiro128+ s)))
    0))
