;; -*- mode: gaz -*-

;; compute the AES S-box (8-bit arithmetic in GF(2^8)), print the first 16 entries.

(define (initialize_aes_sbox:none sbox:(mut (vec 256 i8)))
  (let loop ((p0:i8 1)
             (q0:i8 1))
    (let (;; multiply p by 3
          (p1:i8 (xor p0 (<< p0 1) (if (= #x80 (& p0 #x80)) #x1b #x00)))
          ;; divide q by 3 (equals multiplication by #xf6)
          (q1:i8 (xor q0 (<< q0 1)))
          (q2:i8 (xor q1 (<< q1 2)))
          (q3:i8 (xor q2 (<< q2 4)))
          (q4:i8 (xor q3 (if (= #x80 (& q3 #x80)) #x09 #x00)))
          ;; compute the affine transformation
          (xformed:i8 (xor q4 (<<< q4 1) (<<< q4 2) (<<< q4 3) (<<< q4 4))))
      (set! sbox[p1] (xor xformed #x63))
      (when (<> p1 1)
        (goto loop p1 q4))))
  (set! sbox[0] #x63)
  )

(define (main:i32)
  (let ((sbox:(mut (vec 256 i8)) (alloca)))
    (initialize_aes_sbox sbox)
    (for (i:i32 16)
      (print sbox[i]))
    0))
