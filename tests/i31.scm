;; -*- mode: gaz -*-

;; limb vectors whose length is given by another argument: `(vec len i32)`.
;; a constant-time conditional copy and a 31-bit-limb add with carry,
;;  after BearSSL's i31 code.

(define (MUX:i32 ctl:i32 x:i32 y:i32)
  (xor y (& (- ctl) (xor x y))))

(define (CCOPY:none len:i32 ctl:i32 dst:(mut (vec len i32)) src:(mut (vec len i32)))
  (for (i:i32 len)
    (set! dst[i] (MUX ctl src[i] dst[i]))))

(define (i31/add:i32 len:i32 a:(mut (vec len i32)) b:(mut (vec len i32)) ctl:i32)
  (let loop ((u:i32 0)
             (cc:i32 0))
    (if (< u len)
        (let ((naw:i32 (+ a[u] b[u] cc)))
          (set! a[u] (MUX ctl (& naw #x7fffffff) a[u]))
          (goto loop (+ u 1) (& 1 (>> naw 31))))
        cc)))

(define (main:i32)
  (let ((len:i32 4)
        (a:(mut (vec len i32)) (alloca))
        (b:(mut (vec len i32)) (alloca))
        (c:(mut (vec len i32)) (alloca)))
    (set! a[0] #x7fffffff) (set! a[1] #x7fffffff) (set! a[2] 5) (set! a[3] #x40000000)
    (set! b[0] 1)          (set! b[1] 0)          (set! b[2] 7) (set! b[3] #x40000000)
    (for (i:i32 len)
      (set! c[i] 0))
    ;; ctl = 0: no copy.  ctl = 1: copy.
    (CCOPY len 0 c a)
    (print !c)
    (CCOPY len 1 c a)
    (print !c)
    ;; ctl = 0: a is untouched, but the carry is still computed.
    (print (i31/add len c b 0))
    (print !c)
    (print (i31/add len a b 1))
    (print !a)
    0))
