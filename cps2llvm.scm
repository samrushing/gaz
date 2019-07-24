;; -*- Mode: Irken -*-

;; --------------------------------------------------------------------------------
;; sample direct LLVM output.
;; --------------------------------------------------------------------------------

(defmacro for-list-counting
  (for-list-counting iname vname list body ...)
  -> (let $loop (($list list)
                 (iname 0))
       (match $list with
	 () -> #u
	 (vname . $tl) -> (begin body ... ($loop $tl (+ iname 1)))
	 )))

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
        (cps:letval x V K)       -> (begin (alist/push venv x V) (pass1 K blockname))
        (cps:letcont k xs K L)   -> (begin (pass1 L blockname) (pass1 K k))
        (cps:if x k1 k2)         -> #u
        (cps:appk k xs)          -> (for-list-counting i x xs
                                       (alist/push phimap (:tuple k i) (:tuple x blockname)))
        (cps:dead K)             -> (pass1 K blockname)
        (cps:prim name x vars K) -> (pass1 K blockname)
        (cps:app name k vars)    -> #u
        ))

    (define (emit-phi blockname x idx)
      (let loop ((acc (list:nil))
                 (phimap phimap))
        (match phimap with
          (alist:nil)
          -> (if (> (length acc) 0)
                 (printf "  %" (sym x) " = phi i64 [ " (join " ], [ " acc) " ]\n"))
          (alist:entry (:tuple ktrg idx0) (:tuple x0 ksrc) rest)
          -> (if (and (eq? ktrg blockname) (= idx idx0))
                 (loop (list:cons (format (valref x0) ", %" (sym ksrc)) acc) rest)
                 (loop acc rest))
          )))

    (define (valref x)
      (match (alist/lookup venv x) with
        (maybe:yes v) -> (format (int v))
        (maybe:no)    -> (format "%" (sym x))
        ))

    (define (emit exp blockname)
      (match exp with
        (cps:letval x V K)
        -> (emit K blockname)
        (cps:letcont k xs K L)
        -> (begin
             (emit L blockname)
             ;; note: L is the init, and is in the current block
             (printf "\n" (sym k) ":\n") ;; label
             (for-list-counting i x xs
                (emit-phi k x i))
             (emit K k) ;; with new blockname
             )
        (cps:if x k1 k2)
        -> (let ((r (gensym)))
             (printf "  %" (sym r) " = icmp ne i64 " (valref x) ", 0\n")
             (printf "  switch i1 %" (sym r) ", label %" (sym k1) " [i1 0, label %" (sym k2) "]\n"))
        (cps:appk k xs)
        -> (branch k xs blockname)
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
             (branch k (list r) blockname))
        )
      )

    (define (branch k xs blockname)
      ;; XXX what if |xs| > 1 ?
      (match k with
        'halt -> (printf "  ret i64 " (valref (first xs)) "\n")
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
               (printf "  %" (sym x) " = zext i1 %" (sym r) " to i64\n"))
          (maybe:no)
          -> (match (alist/lookup binop-alist name) with
               (maybe:yes op)
               -> (printf "  %" (sym x) " = " op " i64 " (join ", " args) "\n")
               (maybe:no)
               -> (raise (:NoSuchPrim name))
               ))))

    (printf "define i64 @" (sym name) "("
            (join (lambda (x) (format "i64 %" (sym x))) ", " args)
            ") {\n")
    (printf "top:\n")
    (pass1 exp 'top)
    (emit exp 'top)
    (printf "}\n")
    )
  )
