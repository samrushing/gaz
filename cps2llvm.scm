;; --------------------------------------------------------------------------------
;; sample direct LLVM output.
;; --------------------------------------------------------------------------------

;; for this test I'm just going to emit text.
(define (cpsfun->llvm name args exp)

  (let ((phimap (alist:nil))
        (venv (alist:nil)))

    (define gensym
      (let ((counter 0))
        (lambda ()
          (inc! counter)
          (string->symbol (format "r" (int counter))))))

    (define (pass1 exp blockname)
      (match exp with
        (cps:let name x K)       -> (pass1 K blockname)
        (cps:ref name x K)       -> (pass1 K blockname)
        (cps:set name x K)       -> (pass1 K blockname)
        (cps:letval x V K)       -> (begin (alist/push venv x V) (pass1 K blockname))
        (cps:letcont k x K L)    -> (begin (pass1 L blockname) (pass1 K k))
        (cps:if x k1 k2)         -> #u
        (cps:appk k x)           -> (alist/push phimap k (:tuple x blockname))
        (cps:dead K)             -> (pass1 K blockname)
        (cps:prim name x vars K) -> (pass1 K blockname)
        (cps:app name k vars)    -> #u
        ))

    (define (emit-phi blockname x)
      (let loop ((acc (list:nil))
                 (phimap phimap))
        (match phimap with
          (alist:nil)
          -> (if (> (length acc) 0)
                 (printf "  %" (sym x) " = phi i64 [ " (join " ], [ " acc) " ]\n"))
          (alist:entry ktrg (:tuple x ksrc) rest)
          -> (if (eq? ktrg blockname)
                 (loop (list:cons (format (valref x) ", %" (sym ksrc)) acc) rest)
                 (loop acc rest))
          )))

    (define (valref x)
      (match (alist/lookup venv x) with
        (maybe:yes v) -> (format (int v))
        (maybe:no)    -> (format "%" (sym x))
        ))

    (define (emit exp blockname)
      (match exp with
        (cps:let name x K)
        -> (begin
             (printf "  %u" (sym name) " = alloca i64\n")
             (printf "  store i64 " (valref x) ", i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:ref name x K)
        -> (begin
             (printf "  %" (sym x) " = load i64, i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:set name x K)
        -> (begin
             (printf "  store i64 " (valref x) ", i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:letval x V K)
        -> (emit K blockname)
        (cps:letcont k x K L)
        -> (begin
             (emit L blockname)
             ;; note: L is the init, and is in the current block
             (printf "\n" (sym k) ":\n") ;; label
             (emit-phi k x)              ;; [ %x4, %block ]
             (emit K k)                  ;; with new blockname
             )
        (cps:if x k1 k2)
        -> (let ((r (gensym)))
             (printf "  %" (sym r) " = icmp ne i64 " (valref x) ", 0\n")
             (printf "  switch i1 %" (sym r) ", label %" (sym k1) " [i1 0, label %" (sym k2) "]\n"))
        (cps:appk k x)
        -> (branch k x blockname)
        (cps:dead K)
        -> (emit K blockname)
        (cps:prim name x vars K)
        -> (begin
             (emit-prim name x vars)
             (emit K blockname))
        (cps:app name k vars)
        -> (let ((r (gensym)))
             (printf "  %" (sym r) " = call i64 @" (sym name) " ("
                     (join (lambda (x) (format "i64 " (valref x))) ", " vars)
                     ")\n")
             (branch k r blockname))
        )
      )

    ;; phimap must be done in a separate pass.

    (define (branch k x blockname)
      (match k with
        'halt -> (printf "  ret i64 " (valref x) "\n")
        k     -> (printf "  br label %" (sym k) "\n")
        ))

    (define icmp-alist
      (alist/make
       ('= "eq")
       ('<> "ne")
       ('> "ugt")
       ('>= "uge")
       ('< "ult")
       ('<= "ule")
       ;; for now, no signed arithmetic.
       ))

    (define binop-alist
      (alist/make
       ('+ "add")
       ('- "sub")
       ('* "mul")
       ('/ "udiv")
       ('and "and")
       ('or "or")
       ('xor "xor")
       ('ashr "ashr")
       ('<< "shl")
       ('>> "shr")
       ))

    (define (emit-prim name x vars)
      (let ((args (map valref vars)))
        (match (alist/lookup icmp-alist name) with
          (maybe:yes code)
          -> (let ((r (gensym)))
               (printf "  %" (sym r) " = icmp " code " i64 " (join ", " args) "\n")
               (printf "  %" (sym x) " = zext i1 %r" (sym r) " to i64\n"))
          (maybe:no)
          -> (match (alist/lookup binop-alist name) with
               (maybe:yes op)
               -> (printf "  %" (sym x) " = " op " i64 " (join ", " args) "\n")
               (maybe:no)
               -> (raise (:NoSuchPrim name))
               ))))

    (printf "define i64 @" (sym name) "("
            (join (lambda (x) (format "i64 %u" (sym x))) ", " args)
            ") {\n")
    (printf "top:\n")
    (pass1 exp 'top)
    (emit exp 'top)
    (printf "}\n")
    )
  )
