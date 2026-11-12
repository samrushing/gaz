;; -*- mode: gaz -*-

;; the ChaCha20 block function, with the test vector from RFC 7539 2.3.2.

(defmacro QR
  (QR a b c d)
  -> (begin
       (inc! a b) (set! d (<<< (xor d a) 16))
       (inc! c d) (set! b (<<< (xor b c) 12))
       (inc! a b) (set! d (<<< (xor d a)  8))
       (inc! c d) (set! b (<<< (xor b c)  7))
       ))

(define (chacha20_block:none out:(mut (vec 16 i32)) in:(ref (vec 16 i32)))
  (let ((x:(mut (vec 16 i32)) (alloca)))
    (for (i:i32 16)
      (set! x[i] in[i]))
    (for (i:i32 0 10)
      ;; odd round
      (QR x[0] x[4] x[8]  x[12])
      (QR x[1] x[5] x[9]  x[13])
      (QR x[2] x[6] x[10] x[14])
      (QR x[3] x[7] x[11] x[15])
      ;; even round
      (QR x[0] x[5] x[10] x[15])
      (QR x[1] x[6] x[11] x[12])
      (QR x[2] x[7] x[8]  x[13])
      (QR x[3] x[4] x[9]  x[14])
      )
    (for (i:i32 16)
      (set! out[i] (+ x[i] in[i])))
    ))

(define-constant in:(vec 16 i32) #(
  #x61707865 #x3320646e #x79622d32 #x6b206574
  #x03020100 #x07060504 #x0b0a0908 #x0f0e0d0c
  #x13121110 #x17161514 #x1b1a1918 #x1f1e1d1c
  #x00000001 #x09000000 #x4a000000 #x00000000
  ))

(define (main:i32)
  (let ((out:(mut (vec 16 i32)) (alloca)))
    (chacha20_block out in)
    (for (i:i32 16)
      (print out[i]))
    0))
