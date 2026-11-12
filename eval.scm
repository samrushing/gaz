;; -*- mode: irken -*-

;; CPS interpreter/evaluator.

;; next step: I think we need to use a 'zval' type to hold 'values'.
;; currently, we use zlit, which can hold integers and vectors, but
;; has no way of modeling references.

(datatype zval
  (:big big)
  (:vec (vector zval))
  (:ref {cell=zval})
  (:vref {cell=zval} int)
  )

(define (big->hex bits n)
  (let ((need (how-many bits 4))
        (res (make-vector need #\0))
        (b16 (int->big 16)))
    (for-range-rev i need
      (let (((q r) (big-div n b16)))
        (set! res[i] hex-table[(big->int r)])
        (set! n q)))
    (list->string (vector->list res))))

(define zval-repr
  (type:int (itype:fix bits)) (zval:big x)
  -> (format "0x" (big->hex bits x))
  (type:ref type) (zval:ref r)
  -> (format "|" (zval-repr type r.cell) "|")
  (type:mut type) (zval:ref r)
  -> (format "<" (zval-repr type r.cell) ">")
  (type:vec _ _ ty) (zval:vec xs)
  -> (format "#(" (join (partial (zval-repr ty _)) " " (vector->list xs)) ")")
  (type:ref type) (zval:vref r index)
  -> (format (zval-repr type r.cell) "[" (int index) "]")
  _ _ -> (impossible)
  )

(define (vector-map p v)
  (let ((vlen (vector-length v)))
    (if (= vlen 0)
        #()
        (let ((item0 (p v[0]))
              (r (make-vector vlen item0)))
          (for-range* i 1 vlen
            (set! r[i] (p v[i])))
          r
          ))))

(define zlit->zval
  (zlit:none) -> (zval:big big/0) ;; ?
  (zlit:big n) -> (zval:big n)
  (zlit:vec subs) -> (zval:vec (vector-map zlit->zval subs))
  )

(define zval-zero?
  (zval:big (big:zero)) -> #t
  _                     -> #f
  )

;; we need to model fix-sized unsigned integers.

;; xxxx xxaa aaaa aaaa aaaa
;; we want to set x == 0

;; given the leading edge of digits:
;; xxaa .... ....
;; we want to know how many bits (of that digit) to preserve.

(define (digits-trunc! dx bits)
  (let loop ((xbits (* big/bits (vlen dx)))
             (i 0))
    (let ((extra (- xbits bits)))
      (cond ((<= extra 0)
             #u)
            ((>= extra big/bits)
             (set! dx[i] 0)
             (loop (- xbits big/bits) (+ i 1)))
            (else
             (let ((mask (- (<< 1 (- big/bits extra)) 1)))
               (set! dx[i] (logand dx[i] mask))
               (loop (- xbits big/bits) (+ i 1))))
            ))))

(define big-trunc!
  (big:zero)   bits -> #u
  (big:pos vn) bits -> (digits-trunc! vn bits)
  (big:neg vn) bits -> (raise (:Eval "not implemented" "negative bignums"))
  )

(define (two**n n)
  (big (<< (I 2) n)))

(define (twos-canon bits bn)
  (match bn with
    (big:pos dn) -> (let ((dn0 (copy-vector dn)))
                      (digits-trunc! dn0 bits)
                      (digits->big dn0 #t))
    (big:neg dn) -> (twos-canon bits (big-add (two**n bits) bn))
    (big:zero)   -> (big:zero)
  ))

(define (big-rotl n shift bits)
  (big-add
   (big-lshift n shift)
   (big-rshift n (- bits shift))))

(define (big-rotr n shift bits)
  (big-rotl n (- bits shift) bits))

(define (eval-fun env funmap ftype formals body depth quiet?)

  (let ((kenv (alist:nil)))

    (define (extend env name val)
      (alist:entry name val env))

    (define extend*
      env () () -> env
      env (name . names) (val . vals)
      -> (extend* (extend env (var/name name) val) names vals)
      env names vals
      -> (raise (:Eval "Continuation Arity" (format (int (length names)) " != " (int (length vals)))))
      )

    (define lookup
      env (var:t x tx)
      -> (match (alist/lookup env x) with
           (maybe:yes v) -> v
           (maybe:no)    -> (raise (:Eval "UnknownVar" (format (sym x))))
           ))

    (define (lookup* env args)
      (define R
        acc ()        -> (reverse acc)
        acc (hd . tl) -> (R (list:cons (lookup env hd) acc) tl)
        )
      (R '() args))

    (define fvar
      (var:t x tx) -> (format (ansi blue (sym x)) ":" (ansi yellow (type-repr tx)))
      )

    (define (prim-int-icmp cmp-val inv? a b)
      (zval:big
       (match (eq? (big-cmp a b) cmp-val) inv? with
         #t #t -> big/0
         #t #f -> big/1
         #f #t -> big/1
         #f #f -> big/0
         )))

    (define (prim-icmp cmp-val inv?)
      (lambda (env type args)
        (match type args with
          (type:int _) ((:tuple ta (zval:big a)) (:tuple tb (zval:big b)))
          -> (prim-int-icmp cmp-val inv? a b)
          (type:vec v? size ty) ((:tuple ta (zval:vec va)) (:tuple tb (zval:vec vb)))
          -> (prim-vec-icmp cmp-val inv? va vb)
          _ args
          -> (raise (:Eval "Bad icmp Args" (cmp-repr cmp-val)))
          )))

    (define (prim-vec-icmp cmp-val inv? a b)
      (let ((alen (vector-length a))
            (rvec (make-vector alen (zval:big big/0))))
        (for-range i alen
          (match a[i] b[i] with
            (zval:big ba) (zval:big bb)
            -> (set! rvec[i] (prim-int-icmp cmp-val inv? ba bb))
            _ _
            -> (impossible)
            ))
        (zval:vec rvec)
        ))

    (define (prim-int-binop op bits a b)
      (zval:big
       (twos-canon
        bits
        (match op with
          '+   -> (big-add a b)
          '-   -> (big-sub a b)
          '*   -> (big-mul a b)
          '/   -> (big-quo a b)
          'rem -> (big-rem a b)
          '<<  -> (big-lshift a (big->int b))
          '>>  -> (big-rshift a (big->int b))
          '<<< -> (big-rotl a (big->int b) bits)
          '>>> -> (big-rotr a (big->int b) bits)
          _    -> (raise (:Eval "UnknownIntBinPrimop" (format (sym op))))
          ))))

    (define (prim-vec-binop op bits a b)
      (let ((alen (vector-length a))
            (rvec (make-vector alen (zval:big big/0))))
        (for-range i alen
          (match a[i] b[i] with
            (zval:big ba) (zval:big bb)
            -> (set! rvec[i] (prim-int-binop op bits ba bb))
            _ _
            -> (impossible)
            ))
        (zval:vec rvec)
        ))

    (define (prim-binop op)
      (lambda (env rtype args)
        (match rtype args with
          (type:int (itype:fix bits)) ((:tuple ta (zval:big a)) (:tuple tb (zval:big b)))
          -> (prim-int-binop op bits a b)
          (type:vec v? size (type:int (itype:fix bits))) ((:tuple ta (zval:vec a)) (:tuple tb (zval:vec b)))
          -> (prim-vec-binop op bits a b)
          _ _ -> (raise (:Eval "Binop Arity" (format (sym op))))
          )))

    (define (prim-int-logop op bits a b)
      (let ((a0 (big-add a (two**n bits)))
            (b0 (big-add b (two**n bits)))
            (c0 (two**n bits)))
        (match a0 b0 c0 with
          (big:pos da) (big:pos db) (big:pos dc)
          -> (begin
               (for-range i (vector-length da)
                 (set! dc[i] (logand big/mask (op da[i] db[i]))))
               (zval:big (twos-canon bits c0)))
          _ _ _
          -> (raise (:Eval "Bad Bignum Operands" "logop"))
          )))

    (define (prim-logop op)
      (lambda (env rtype args)
        (match rtype args with
          (type:int (itype:fix bits)) ((:tuple ta (zval:big a)) (:tuple tb (zval:big b)))
          -> (prim-int-logop op bits a b)
          (type:vec v? size (type:int (itype:fix bits))) ((:tuple ta (zval:vec a)) (:tuple tb (zval:vec b)))
          -> (prim-vec-logop op bits a b)
          _ _ -> (raise (:Eval "Bad Logop Arity" ""))
          )))

    (define (prim-vec-logop op bits a b)
      (let ((alen (vector-length a))
            (rvec (make-vector alen (zval:big big/0))))
        (for-range i alen
          (match a[i] b[i] with
            (zval:big ba) (zval:big bb)
            -> (set! rvec[i] (prim-int-logop op bits ba bb))
            _ _
            -> (impossible)
            ))
        (zval:vec rvec)
        ))

    (define zval->int
      (zval:big n) -> (big->int n)
      _ -> (impossible)
      )

    (define prim-shufv
      env t ((:tuple tv0 (zval:vec v0)) (:tuple tv1 (zval:vec v1)) (:tuple tm (zval:vec m)))
      -> (let ((vlen (vector-length v0))
               (mlen (vector-length m))
               (rvec (make-vector mlen (zval:big big/0))))
           (for-range i mlen
             (let ((j (zval->int m[i])))
               (if (< j vlen)
                   (set! rvec[i] v0[j])
                   (set! rvec[i] v1[(- j vlen)]))))
           (zval:vec rvec))
      env t ((:tuple tv0 (zval:vec v0)) (:tuple tm (zval:vec m)))
      -> (let ((mlen (vector-length m))
               (rvec (make-vector mlen (zval:big big/0))))
           (for-range i mlen
             (set! rvec[i] v0[(zval->int m[i])]))
           (zval:vec rvec))
      env t args -> (impossible)
      )

    (define prim-get
      env t ((:tuple tv (zval:ref r))) -> r.cell
      env t ((:tuple tv (zval:vref {cell=(zval:vec v)} i))) -> v[i]
      ;; hack: pass-through %get
      env t ((:tuple tv v)) -> v
      env t args -> (impossible)
      )

    (define prim-set
      env t ((:tuple tv (zval:ref r)) (:tuple tx x))
      -> (begin (set! r.cell x) (zval:big big/0))
      env t ((:tuple tv (zval:vref {cell=(zval:vec v)} i)) (:tuple tx x))
      -> (begin (set! v[i] x) (zval:big big/0))
      env t args
      -> (impossible)
      )

    (define prim-vref
      env rtype ((:tuple tvec (zval:ref {cell=v})) (:tuple ti (zval:big index)))
      -> (zval:vref {cell=v} (big->int index))
      env rtype ((:tuple tvec (zval:vec v)) (:tuple ti (zval:big index)))
      -> v[(big->int index)]
      _ _ _
      -> (impossible)
      )

    (define (build-type env t)
      (match t with
        (type:none)          -> (zval:big big/0)
        (type:int _)         -> (zval:big big/0)
        (type:ref t)         -> (zval:ref {cell=(build-type env t)})
        (type:mut t)         -> (zval:ref {cell=(build-type env t)})
        (type:vec v? size t) -> (zval:vec
                                 (list->vector
                                  (map
                                   (lambda (x) (build-type env t))
                                   (range (get-size env size)))))
        t -> (raise (:Eval "Bad Type" (type-repr t)))
        ))

    (define get-size
      env (itype:fix size) -> size
      env (itype:dyn name) -> (begin
                                (trace (printf "get-size: " (sym name) "\n"))
                                (match (alist/lookup env name) with
                                  (maybe:yes (:tuple tv v))
                                  -> (zval->int v)
                                  (maybe:no)
                                  -> (raise (:Eval "failed to look up ityp:dyn size" ""))
                                  ))
      env _ -> (impossible)
      )

    (define prim-alloca
      env t ()
      -> (build-type env t)
      env t args
      -> (raise (:Eval "alloca: Bad Args" ""))
      )

    (define print-int
      ;; XXX print this at correct bit-width in hex.
      env ty ((:tuple tx x)) -> (begin (printf (bold (zval-repr tx x)) "\n") (zval:big (big:zero)))
      env ty _   -> (impossible)
      )

    (define prim-alist
      (alist/make
       ('=     (prim-icmp (cmp:=) #f))
       ('<>    (prim-icmp (cmp:=) #t))
       ('>     (prim-icmp (cmp:>) #f))
       ('<     (prim-icmp (cmp:<) #f))
       ('>=    (prim-icmp (cmp:<) #t))
       ('<=    (prim-icmp (cmp:>) #t))
       ('+     (prim-binop '+))
       ('-     (prim-binop '-))
       ('*     (prim-binop '*))
       ('/     (prim-binop '/))
       ('rem   (prim-binop 'rem))
       ('<<    (prim-binop '<<))
       ('>>    (prim-binop '>>))
       ('>>>   (prim-binop '>>>))
       ('<<<   (prim-binop '<<<))
       ('xor   (prim-logop logxor))
       ('or    (prim-logop logior))
       ('and   (prim-logop logand))
       ('shufv prim-shufv)
       ('%get  prim-get)
       ('%set! prim-set)
       ('%vref prim-vref)
       ('alloca prim-alloca)
       ('print_i32 print-int)
       ('print print-int)
       ))

    (define EK
      env kenv (cvar:t k) args
      -> (match (alist/lookup kenv k) with
           (maybe:no)
           -> (raise (:Eval "Unknown Continuation" (format (sym k))))
           (maybe:yes (:tuple vars K))
           -> (E (extend* env vars (lookup* env args)) kenv K)
           ))

    (defmacro quietf
      (quietf a ...) -> (if quiet? #u (printf a ...))
      )

    (define E-prim
      env kenv prim (var:t r tr) args K
      -> (match (alist/lookup prim-alist prim) with
           (maybe:yes fun)
           -> (let ((vals (lookup* env args))
                    (rval (fun env tr vals)))
                (E (extend env r (:tuple tr rval)) kenv K))
           (maybe:no)
           -> (match (tree/member funmap symbol-index-cmp prim) with
                (maybe:yes (:tuple ftype formals body))
                -> (let ((vals0 (lookup* env args))
                         (env0 (extend* env formals vals0)))
                     (quietf (repeat depth "  ") "CALL " (ansi red (sym prim))
                             " (" (join fvar ", " formals) ")\n")
                     (E (extend
                         env r
                         (:tuple tr
                                 (eval-fun env0 funmap
                                           ftype formals body
                                           (+ depth 1)
                                           quiet?
                                           )))
                        kenv K))
                (maybe:no)
                -> (raise (:Eval "Unknown Prim" (format (sym prim))))
                )))

    (define (E env kenv exp)
      (quietf (repeat depth "  "))
      (match exp with
        (cps:prim name param var args K)
        -> (begin
             (quietf "PRIM " (fvar var) " = " (sym name) " (" (join fvar ", " args) ")\n")
             (E-prim env kenv name var args K))
        (cps:letval (var:t x tx) V K)
        -> (begin
             (quietf "LET  " (fvar (var:t x tx)) " = " (zlit-repr V) "\n")
             (E (extend env x (:tuple tx (zlit->zval V))) kenv K))
        (cps:appk (cvar:t 'halt) (r))
        -> (let (((tv v) (lookup env r)))
             (quietf "HALT " (zval-repr tv v) ":" (type-repr tv) "\n")
             v) ;; return value for this function.
        (cps:appk (cvar:t 'halt) ())
        -> (begin
             (quietf "HALT [no result]\n")
             (zval:big big/0))
        (cps:appk (cvar:t k) args)
        -> (begin
             (quietf "GOTO " (ansi green (sym k)) " (" (join fvar ", " args) ")\n")
             (EK env kenv (cvar:t k) args))
        (cps:letcont (cvar:t k) vars K L)
        -> (begin
             (quietf "CONT " (ansi green (sym k)) "\n")
             (E env (alist:entry k (:tuple vars K) kenv) L))
        (cps:if x k0 k1)
        -> (let (((tv v) (lookup env x)))
             (quietf "TEST " (zval-repr tv v) ":" (type-repr tv) " "
                     (sym (cvar/name k0)) " " (sym (cvar/name k1)) "\n")
             (EK env kenv (if (zval-zero? v) k1 k0) '()))
        (cps:dead K)
        -> (begin
             (quietf "DEAD\n")
             (E env kenv K))
        other
        -> (begin
             (printf "not yet implemented\n")
             (zval:big big/0))
        ))

    (E env kenv body)
    ))

(define (make-funmap funs)
  (let ((funmap (tree/empty)))
    (for-list item funs
      (match item with
        (:tuple fname ftype formals body)
        -> (tree/insert! funmap symbol-index-cmp fname (:tuple ftype formals body))
        ))
    funmap))

(define (make-litenv lits)
  (let ((env (alist:nil)))
    (for-list pair lits
      (match pair with
        (:tuple name vtype val)
        -> (alist/push env name (:tuple vtype (zval:ref {cell=(zlit->zval val)})))
        ))
    env))

(define (eval tenv funs lits quiet?)
  (let ((funmap (make-funmap funs))
        (env (make-litenv lits)))
    (match (tree/member funmap symbol-index-cmp 'main) with
      (maybe:yes (:tuple ftype formals body))
      -> (begin
           (verbose (printf (ansi green "evaluating...\n")))
           (eval-fun env funmap ftype formals body 0 quiet?)
           0)
      (maybe:no)
      -> (begin
           (printf (bold "eval: no main function.\n"))
           0)
      )))
