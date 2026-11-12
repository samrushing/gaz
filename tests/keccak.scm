;; -*- mode: gaz -*-

;; the Keccak-f[1600] permutation (after tiny_sha3), applied to the zero state.

(define-constant KECCAKF_ROUNDS:i32 24)

(define-constant keccakf_rndc:(vec 24 i64) #(
    #x0000000000000001 #x0000000000008082 #x800000000000808a
    #x8000000080008000 #x000000000000808b #x0000000080000001
    #x8000000080008081 #x8000000000008009 #x000000000000008a
    #x0000000000000088 #x0000000080008009 #x000000008000000a
    #x000000008000808b #x800000000000008b #x8000000000008089
    #x8000000000008003 #x8000000000008002 #x8000000000000080
    #x000000000000800a #x800000008000000a #x8000000080008081
    #x8000000000008080 #x0000000080000001 #x8000000080008008
    ))

(define-constant keccakf_rotc:(vec 24 i64)
  #(1 3 6 10 15 21 28 36 45 55 2 14 27 41 56 8 25 43 62 18 39 61 20 44)
  )

(define-constant keccakf_piln:(vec 24 i32)
  #(10 7 11 17 18 3 5 16 8 21 24 4 15 23 19 13 12 2 20 14 22 9 6 1)
  )

(define (sha3_keccakf0:none st:(mut (vec 25 i64)))
  (let ((bc:(mut (vec 5 i64)) (alloca)))
    (for (r:i32 KECCAKF_ROUNDS)
      ;; theta
      (for (i:i32 5)
        (set! bc[i] (xor st[i] st[(+ i 5)] st[(+ i 10)] st[(+ i 15)] st[(+ i 20)])))
      (for (i:i32 5)
        (let ((t:i64 (xor bc[(mod (+ i 4) 5)] (<<< bc[(mod (+ i 1) 5)] 1))))
          (for (j:i32 5)
            (set! st[(+ (* j 5) i)] (xor st[(+ (* j 5) i)] t)))))
      ;; rho pi
      (let loop ((t:i64 st[1])
                 (i:i32 0))
        (if (< i 24)
            (let ((j:i32 keccakf_piln[i]))
              (set! bc[0] st[j])
              (set! st[j] (<<< t keccakf_rotc[i]))
              (goto loop bc[0] (+ i 1)))))
      ;; chi
      (for (j:i32 5)
        (for (i:i32 5)
          (set! bc[i] st[(+ i (* j 5))]))
        (for (i:i32 5)
          (set! st[(+ i (* j 5))]
                (xor st[(+ i (* j 5))]
                     (& (~ bc[(mod (+ i 1) 5)]) bc[(mod (+ i 2) 5)])))))
      ;; iota
      (set! st[0] (xor st[0] keccakf_rndc[r]))
      )))

(define (main:i32)
  (let ((st:(mut (vec 25 i64)) (alloca)))
    (for (i:i32 25)
      (set! st[i] 0))
    (sha3_keccakf0 st)
    (for (i:i32 25)
      (print st[i]))
    0))
