;; -*- mode: gaz -*-

;; arithmetic on whole vectors: the operators apply element-wise.

(declare print:(-> none ((vec 5 i32))))

(define (main:i32)
  (let ((v0:(vec 5 i32) #(0 1 2 3 4))
        (v1:(vec 5 i32) #(9 8 7 6 5))
        (v2:(vec 5 i32) #(#xdeadbeef #xfeedbeef #xcafed00f #xbadab00f #xdadacafe))
        (v3:(vec 5 i32) #(1 2 3 4 5))
        )
    (print (+ v0 v1))
    (print (xor v0 v1))
    (print (<< v1 v0))
    (print (<<< v2 v3))
    0
    ))
