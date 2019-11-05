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

  ;; format a type for llvm.
  (define (ftype t)
    (match (apply-subst t) with
      (type:int w _)                   -> (format "i" (int w))
      (type:vec size t _)              -> (format "<" (int size) " x " (ftype t) ">")
      ;; (type:ref (type:vec size t _) _) -> (format "[" (int size) " x " (ftype t) "]")
      (type:ref t _)                   -> (format (ftype t) "*")
      (type:none _)                    -> "void"
      _                                -> (raise (:BadLLVMType (repr (type->sexp t))))
      ))

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
          (cps:prim name p x vars K)      -> (pass1 K blockname)
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
          (cps:prim name p x vars K)
          -> (begin (emit-prim name p x vars) (emit K blockname))
          (cps:app name k vars)
          -> (raise (:LLVM/NotImplementedYet))
          )
        )

      (define (branch k xs blockname)
        ;; XXX what if |xs| > 1 ?
        (match k (var->type (first xs)) with
          (cvar:t 'halt) (type:none _) -> (oprintf "  ret void\n")
          (cvar:t 'halt) _             -> (oprintf "  ret " (valreft (first xs)) "\n")
          (cvar:t k)     _             -> (oprintf "  br label %" (sym k) "\n")
          ))

      (define prim-alist
        (alist/make
         ('=     (prim-icmp "eq"))
         ('<>    (prim-icmp "ne"))
         ('>     (prim-icmp "ugt"))
         ('>=    (prim-icmp "uge"))
         ('<     (prim-icmp "ult"))
         ('<=    (prim-icmp "ule"))
         ('+     (prim-binop "add"))
         ('-     (prim-binop "sub"))
         ('*     (prim-binop "mul"))
         ('/     (prim-binop "udiv"))
         ('and   (prim-binop "and"))
         ('or    (prim-binop "or"))
         ('xor   (prim-binop "xor"))
         ('ashr  (prim-binop "ashr"))
         ('<<    (prim-binop "shl"))
         ('>>    (prim-binop "lshr"))
         ('set!   prim-set!)
         ('%vref  prim-vref)
         ('%get   prim-%get)
         ('zext   prim-zext)
         ('alloca prim-alloca)
         ))

      (define (prim-binop op)
        (lambda (param r tr args)
          (oprintf "  %" (sym r) " = " op " " (fargst args) "\n")))

      (define (prim-icmp code)
        (lambda (param r tr args)
          (oprintf "  %" (sym r) " = icmp " code " " (fargst args) "\n")))

      (define (prim-set! param r _ args)
        (match args with
          (dst src)
          -> (oprintf "  store " (valreft src) ", " (valreft dst) "\n")
          _
          -> (imp)
          ))

      (define (prim-vref param r tr args)
        (match args with
          ((var:t vec (type:ref tvec _)) index)
          -> (match index with
               (var:t ix (type:int isize _))
               -> (oprintf "  %" (sym r) " = getelementptr "
                           (ftype tvec) ", "
                           (ftype tvec) "* %" (sym vec)
                           ", i32 0, i" (int (if (= 0 isize) 32 isize)) " " (valref index) "\n"
                           )
               _ -> (imp))
          _ -> (imp)
          ))

      (define (prim-%get param r tr args)
        (match args with
          ((var:t p (type:ref tp _)))
          -> (oprintf "  %" (sym r) " = load " (ftype tp) ", " (ftype tp) "* " (valref (first args)) "\n")
          _
          -> (imp)
          ))

      (define (prim-zext param r tr args)
        (match (parse-type param) with
          (:tuple src (type:int osize _))
          -> (oprintf "  %" (sym r) " = zext " (valreft (first args)) " to i" (int osize) "\n")
          _
          -> (imp)
          ))

      (define (prim-alloca param r tr args)
        (match (parse-type param) with
          (:tuple src type)
          -> (oprintf "  %" (sym r) " = alloca " (ftype type) ", i32 1\n")
          ))

      (define var->type
        (var:t _ type) -> (apply-subst type)
        )

      ;; format a set of args with one type, e.g. "i32 %a, %b"
      (define (fargst args)
        (match args with
          ((var:t a ta) . tl)
          -> (format (ftype ta) " " (join valref ", " args))
          ()
          -> (raise (:LLVM/EmptyArgs))
          ))

      (define emit-prim
        name param (var:t x tx) args
        -> (match (alist/lookup prim-alist name) with
             (maybe:yes fun)
             -> (fun param x tx args)
             (maybe:no)
             -> (raise (:LLVM/NoSuchPrim (format (sym name))))
             ))

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
