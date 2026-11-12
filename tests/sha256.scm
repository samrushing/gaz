;; -*- mode: gaz -*-

;; the SHA-256 compression function, applied to the padded block for "abc".

(define-constant K:(vec 64 i32) #(
   #x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5 #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
   #xd807aa98 #x12835b01 #x243185be #x550c7dc3 #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
   #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
   #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7 #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
   #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13 #x650a7354 #x766a0abb #x81c2c92e #x92722c85
   #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3 #xd192e819 #xd6990624 #xf40e3585 #x106aa070
   #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5 #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
   #x748f82ee #x78a5636f #x84c87814 #x8cc70208 #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2
   ))

(define (sha2-round:none H:(mut (vec 8 i32)) B:(ref (vec 16 i32)))
  (let ((w:(mut (vec 64 i32)) (alloca)))
    (for (i:i32 16)
      (set! w[i] B[i]))
    (for (i:i32 16 64)
      (let ((a:i32 w[(- i 15)])
            (b:i32  w[(- i 2)])
            (s0:i32 (xor (>>> a 7) (>>> a 18) (>> a 3)))
            (s1:i32 (xor (>>> b 17) (>>> b 19) (>> b 10))))
        (set! w[i] (+ w[(- i 16)] s0 w[(- i 7)] s1))))
    (let loop ((a:i32 H[0]) (b:i32 H[1]) (c:i32 H[2]) (d:i32 H[3])
               (e:i32 H[4]) (f:i32 H[5]) (g:i32 H[6]) (h:i32 H[7])
               (i:i32 0))
      (if (< i 64)
          (let ((S1:i32 (xor (>>> e 6) (>>> e 11) (>>> e 25)))
                (ch:i32 (xor (& e f) (& (~ e) g)))
                (t1:i32 (+ h S1 ch K[i] w[i]))
                (S0:i32 (xor (>>> a 2) (>>> a 13) (>>> a 22)))
                (maj:i32 (xor (& a b) (& a c) (& b c)))
                (t2:i32 (+ S0 maj)))
            (goto loop (+ t1 t2) a b c (+ d t1) e f g (+ i 1)))
          (begin
            (inc! H[0] a) (inc! H[1] b) (inc! H[2] c) (inc! H[3] d)
            (inc! H[4] e) (inc! H[5] f) (inc! H[6] g) (inc! H[7] h)
            )))))

(define-constant H0:(vec 8 i32) #(
   #x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19
   ))

;; "abc", padded.
(define-constant abc:(vec 16 i32) #(
   #x61626380 0 0 0 0 0 0 0 0 0 0 0 0 0 0 #x00000018
   ))

(define (main:i32)
  (let ((H:(mut (vec 8 i32)) (alloca)))
    (for (i:i32 8)
      (set! H[i] H0[i]))
    (sha2-round H abc)
    (for (i:i32 8)
      (print H[i]))
    0))
