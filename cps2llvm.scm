;; -*- Mode: Irken -*-

;; --------------------------------------------------------------------------------
;; LLVM output.
;; --------------------------------------------------------------------------------

(defmacro for-list-counting
  (for-list-counting iname vname list body ...)
  -> (let $loop (($list list)
                 (iname 0))
       (match $list with
	 () -> #u
	 (vname . $tl) -> (begin body ... ($loop $tl (+ iname 1)))
	 )))

(defmacro oprintf
  (oprintf x ...)
  -> (file/write ofile (format x ...))
  )

(define (compiled->llvm path tenv funs)

  (define (make-opath path)
    (let ((parts (string-split path #\.)))
      (match (reverse parts) with
        ("scm" . rest)
        -> (string-join (reverse (list:cons "ll" rest)) ".")
        (ext . rest)
        -> (raise (:UnexpectedExtension ext))
        ()
        -> (raise (:EmptyPath?))
        )))

  (define (cpsfun->llvm ofile tenv name rtype args exp)

    (let ((phimap (alist:nil))
          (venv (alist:nil)))

      (define gensym
        (let ((counter 0))
          (lambda ()
            (inc! counter)
            (string->symbol (format "r" (int counter))))))

      (define (pass1 exp blockname)
        (match exp with
          (cps:letval (var:t x tx) V K)   -> (begin (alist/push venv x (:tuple tx V)) (pass1 K blockname))
          (cps:letcont (cvar:t k) xs K L) -> (begin (pass1 L blockname) (pass1 K k))
          (cps:if x k1 k2)                -> #u
          (cps:appk (cvar:t k) xs)        -> (for-list-counting i x xs
                                                (alist/push phimap (:tuple k i) (:tuple x blockname)))
          (cps:dead K)                    -> (pass1 K blockname)
          (cps:prim name x vars K)        -> (pass1 K blockname)
          (cps:app name k vars)           -> #u
          ))

      (define (emit-phi blockname x idx)
        (let loop ((acc (list:nil))
                   (phimap phimap))
          (match phimap with
            (alist:nil)
            -> (when (> (length acc) 0)
                 (oprintf "  %" (sym (var/name x)) " = phi " (ftype (var/type x))
                          " [ " (join " ], [ " acc) " ]\n"))
            (alist:entry (:tuple ktrg idx0) (:tuple x0 ksrc) rest)
            -> (if (and (eq? ktrg blockname) (= idx idx0))
                   (loop (list:cons (format (valref x0) ", %" (sym ksrc)) acc) rest)
                   (loop acc rest))
            )))

      ;; format a type for llvm.
      (define (ftype t)
        (match (apply-subst t) with
          (type:int w _)      -> (format "i" (int w))
          (type:vec size t _) -> (format "<" (int size) " x " (ftype t) ">")
          _              -> (raise (:BadLLVMType (repr (type->sexp t))))
          ))

      ;; a reference is to either a name or a value (e.g. "%r3" or "7")
      (define valref
        (var:t x tx)
        -> (match (alist/lookup venv x) with
             (maybe:yes (:tuple tv v)) -> (format (int v))
             (maybe:no)                -> (format "%" (sym x))
             ))

      ;; same thing, but with the type as a prefix (e.g. "i64 %r2")
      (define valreft
        (var:t x tx)
        -> (match (alist/lookup venv x) with
             ;; XXX assert tv == tx?
             (maybe:yes (:tuple tv v)) -> (format (ftype tv) " " (int v))
             (maybe:no)                -> (format (ftype tx) " %" (sym x))
             ))

      (define fcont
        (cvar:t name) -> (format (sym name))
        )

      (define (emit exp blockname)
        (match exp with
          (cps:letval x V K)
          -> (emit K blockname)
          (cps:letcont (cvar:t k) xs K L)
          -> (begin
               (emit L blockname)
               ;; note: L is the init, and is in the current block
               (oprintf "\n" (sym k) ":\n") ;; label
               (for-list-counting i x xs
                                  (emit-phi k x i))
               (emit K k) ;; with new blockname
               )
          (cps:if x k1 k2)
          -> (oprintf "  switch " (valreft x) ", label %" (fcont k1) " [i1 0, label %" (fcont k2) "]\n")
          (cps:appk k xs)
          -> (branch k xs blockname)
          (cps:dead K)
          -> (emit K blockname)
          (cps:prim name x vars K)
          -> (begin (emit-prim name x vars) (emit K blockname))
          (cps:app name k vars)
          -> (raise (:LLVM/NotImplementedYet))
          )
        )

      (define (branch k xs blockname)
        ;; XXX what if |xs| > 1 ?
        (match k with
          (cvar:t 'halt) -> (oprintf "  ret " (valreft (first xs)) "\n")
          (cvar:t k)     -> (oprintf "  br label %" (sym k) "\n")
          ))

      (define icmp-alist
        (alist/make
         ('=  "eq")
         ('<> "ne")
         ('>  "ugt")
         ('>= "uge")
         ('<  "ult")
         ('<= "ule")
         ;; for now, no signed arithmetic.
         ))

      (define binop-alist
        (alist/make
         ('+    "add")
         ('-    "sub")
         ('*    "mul")
         ('/    "udiv")
         ('and  "and")
         ('or   "or")
         ('xor  "xor")
         ('ashr "ashr")
         ('<<   "shl")
         ('>>   "lshr")
         ))

      ;; format a set of args with one type, e.g. "i32 %a, %b"
      (define (fargst args)
        (match args with
          ((var:t a ta) . tl)
          -> (format (ftype ta) " " (join valref ", " args))
          ()
          -> (raise (:LLVM/EmptyArgs))
          ))

      (define emit-prim
        name (var:t x tx) args
        -> (match (alist/lookup icmp-alist name) with
             (maybe:yes code)
             -> (oprintf "  %" (sym x) " = icmp " code " " (fargst args) "\n")
             (maybe:no)
             -> (match (alist/lookup binop-alist name) with
                  (maybe:yes op)
                  -> (oprintf "  %" (sym x) " = " op " " (fargst args) "\n")
                  (maybe:no)
                  -> (match (alist/lookup tenv name) with
                       (maybe:yes (type:arrow rtype argtypes _))
                       -> (oprintf "  %" (sym x) " = call " (ftype rtype)
                                   " @" (sym name) "(" (join valreft ", " args) ")\n")
                       _
                       -> (raise (:LLVM/NoSuchPrim (format (sym name))))
                       ))))

      (define faztname
        (aztname:t name type src)
        -> (format (ftype type) " %" (sym name))
        )

      (oprintf "define " (ftype rtype) " @" (sym name) " (" (join faztname ", " args) ") {\n")
      (oprintf "top:\n")
      (pass1 exp 'top)
      (emit exp 'top)
      (oprintf "}\n")
      )
    )

  (let ((opath (make-opath path))
        (ofile (file/open-write opath #t #o644)))
    ;; emit declarations first
    (for-alist name type tenv
      (match type with
        (type:arrow rtype argtypes _)
        -> (oprintf "declare " (ftype rtype) " @" (sym name) "(" (join ftype ", " argtypes) ")\n")
        _
        -> (raise (:UnexpectedDeclaration (repr (type->sexp type))))
        ))
    ;; emit functions
    (for-list fun funs
      (match fun with
        (:tuple name rtype formals cps)
        -> (cpsfun->llvm ofile tenv name rtype formals cps)
        ))
    (file/flush ofile)
    (file/close ofile)
    ))
