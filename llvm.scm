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
  -> (begin
       (file/write ofile (format x ...))
       ;; XXX DO NOT LEAVE THIS HERE
       (file/flush ofile)
       )
  )

(define (clean s)
  (define safe? (char-class (cons #\_ (append letters digits))))
  (define safe-map
    (alist/make
     (#\? "_question")
     (#\* "_splat")
     (#\+ "_plus")
     (#\- "_dash")
     (#\/ "_slash")
     (#\< "_lt")
     (#\> "_gt")
     (#\^ "_up")
     (#\& "_amp")
     (#\% "_percent")
     (#\@ "_at")
     (#\! "_bang")
     (#\~ "_tilde")
     (#\` "_backtick")
     (#\$ "_dolla")
     ))
  (define (replace ch)
    (match (alist/lookup safe-map ch) with
      (maybe:yes r) -> r
      (maybe:no)    -> (char->string ch)
      ))
  (let ((s (string->list s)))
    (if (all? safe? s)
        (list->string s)
        (string-concat (map replace s)))))

(define (compiled->llvm path tenv funs lits)

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

  (let ((opath (make-opath path))
        (ofile (file/open-write opath #t #o644))
        ;; decls for type-variant intrinsics.
        (decls (cmap/make string-cmp))
        (names (tree/empty))
        (local '()))

    ;; format a type for llvm.
    (define (ftype* asvec? t)
      (match asvec? (apply-subst t) with
        #t (type:vec (itype:fix s) t) -> (format "<" (int s) " x " (ftype* #f t) ">")
        #f (type:vec (itype:fix s) t) -> (format "[" (int s) " x " (ftype* #f t) "]")
        _  (type:int (itype:fix w))   -> (format "i" (int w))
        _  (type:ref t)               -> (format (ftype* #f t) "*")
        _  (type:mut t)               -> (format (ftype* #f t) "*")
        _  (type:none)                -> "void"
        _  _                          -> (raise (:BadLLVMType (repr (type->sexp t))))
        ))

    (define (ftype t)
      (ftype* #t t))

    (define (ftypenv t)
      (ftype* #f t))

    ;; for valref[t] (i.e., 'immediate' literals).
    ;; compare format-lit below.
    (define flit
      ftype? (type:vec size type) (zlit:vec subs)
      -> (format "<" (join (lambda (x) (flit #t type x)) ", " (vector->list subs)) ">")
      ftype? ty (zlit:big n)
      -> (format (if ftype? (format (ftype ty) " ") "") (big->dec n))
      ftype? ty (zlit:none)
      -> (raise (:LLVM/NoneLit))
      _ _ _
      -> (imp)
      )


    (define (safe name)
      (match (tree/member names symbol-index-cmp name) with
        (maybe:yes val) -> val
        (maybe:no)
        -> (let ((name0 (clean (symbol->string name))))
             (tree/insert! names symbol-index-cmp name name0)
             name0)
        ))

    (define (cpsfun->llvm ofile tenv name rtype args exp)

      (let ((phimap (alist:nil))
            (venv (alist:nil)))

        (define gensym
          (let ((counter 0))
            (lambda ()
              (inc! counter)
              (format "%tmp" (int counter)))))

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
                   (oprintf "  %" (safe (var/name x)) " = phi " (ftype (var/type x))
                            " [ " (join " ], [ " acc) " ]\n"))
              (alist:entry (:tuple ktrg idx0) (:tuple x0 ksrc) rest)
              -> (if (and (eq? ktrg blockname) (= idx idx0))
                     (loop (list:cons (format (valref x0) ", %" (safe ksrc)) acc) rest)
                     (loop acc rest))
              )))

        ;; a reference is to either a name or a value (e.g. "%r3" or "7")
        (define valref
          (var:t x tx)
          -> (match (alist/lookup venv x) with
               (maybe:yes (:tuple tv v)) -> (flit #f tv v)
               (maybe:no)
               -> (match (alist/lookup tenv x) with
                    (maybe:yes _) -> (format "@" (safe x))
                    (maybe:no)    -> (format "%" (safe x))
                    )))

        ;; same thing, but with the type as a prefix (e.g. "i64 %r2")
        (define valreft
          (var:t x tx)
          -> (match (alist/lookup venv x) with
               ;; special case for vector literals
               (maybe:yes (:tuple (type:vec size tv) v)) -> (flit #t (type:vec size tv) v)
               (maybe:yes (:tuple tv v)) -> (format (ftype tv) " " (flit #f tv v))
               (maybe:no)
               -> (match (alist/lookup tenv x) with
                    (maybe:yes _) -> (format (ftype tx) " @" (safe x))
                    (maybe:no)    -> (format (ftype tx) " %" (safe x))
                    )
               ))

        (define fcont
          (cvar:t name) -> (format (safe name))
          )

        (define (emit exp blockname)
          (match exp with
            (cps:letval x V K)
            -> (emit K blockname)
            (cps:letcont (cvar:t k) xs K L)
            -> (begin
                 (emit L blockname)
                 ;; note: L is the init, and is in the current block
                 (oprintf "\n" (safe k) ":\n") ;; label
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
          (match k xs with
            (cvar:t 'halt) () ;; guaranteed by strip-void
            -> (oprintf "  ret void\n")
            (cvar:t 'halt) (one)
            -> (oprintf "  ret " (valreft one) "\n")
            (cvar:t 'halt) _
            -> (raise (:LLVM/MultipleReturnValues))
            (cvar:t k) _
            -> (oprintf "  br label %" (safe k) "\n")
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
           ('rem   (prim-binop "urem"))
           ;; I think these need c-style names in order to avoid
           ;;   the obvious conflict with logical and/or/not.
           ('and   (prim-binop "and"))
           ('or    (prim-binop "or"))
           ('xor   (prim-binop "xor"))
           ('ashr  (prim-binop "ashr"))
           ('<<    (prim-binop "shl"))
           ('>>    (prim-binop "lshr"))
           ;; XXX these could become macros over a funnel-shift prim
           ('>>>   (prim-rotate #t))
           ('<<<   (prim-rotate #f))
           ('%set!  prim-set!)
           ('%vref  prim-vref)
           ('%get   prim-%get)
           ('zext   prim-zext)
           ('trunc  prim-trunc)
           ('alloca prim-alloca)
           ))

        (define (prim-binop op)
          (lambda (param r tr args)
            (oprintf "  %" (safe r) " = " op " " (fargst args) "\n")))

        (define (prim-icmp code)
          (lambda (param r tr args)
            (oprintf "  %" (safe r) " = icmp " code " " (fargst args) "\n")))

        (define (prim-set! param r _ args)
          (match args with
            (dst src)
            -> (oprintf "  store " (valreft src) ", " (valreft dst) "\n")
            _
            -> (imp)
            ))

        (define ref/mut->type
          (type:ref t) -> t
          (type:mut t) -> t
          _ -> (impossible)
          )

        ;; getelementptr interprets index values as _signed_, which definitely
        ;;   causes problems for i8 & i16.  Cast these to i32 before using them.
        (define (maybe-unsign-index index)
          (match index with
            (var:t ix (type:int (itype:fix isize)))
            -> (if (>= isize 32)
                   (valreft index)
                   (let ((tmp (gensym)))
                     (oprintf "  " tmp " = zext " (valreft index) " to i32\n")
                     (format "i32 " tmp)))
            _
            -> (imp)
            ))

        (define (prim-vref param r tr args)
          (match args with
            ((var:t vec tvec) index)
            -> (let ((index0 (maybe-unsign-index index)))
                 (oprintf "  %" (safe r) " = getelementptr "
                          (ftypenv (ref/mut->type tvec)) ", "
                          (valreft (first args))
                          ", i32 0, " index0 "\n"))
            _ -> (imp)
            ))

        (define (prim-%get param r tr args)
          (match args with
            ((var:t p (type:ref tp)))
            -> (oprintf "  %" (safe r) " = load " (ftypenv tp) ", " (ftypenv tp) "* " (valref (first args)) "\n")
            ((var:t p (type:mut tp)))
            -> (oprintf "  %" (safe r) " = load " (ftypenv tp) ", " (ftypenv tp) "* " (valref (first args)) "\n")
            _
            -> (imp)
            ))

        (define (prim-zext param r tr args)
          (match (parse-type param) with
            (type:int (itype:fix osize))
            -> (oprintf "  %" (safe r) " = zext " (valreft (first args)) " to i" (int osize) "\n")
            _
            -> (imp)
            ))

        (define (prim-trunc param r tr args)
          (match (parse-type param) with
            (type:int (itype:fix osize))
            -> (oprintf "  %" (safe r) " = trunc " (valreft (first args)) " to i" (int osize) "\n")
            _
            -> (imp)
            ))

        (define (prim-alloca param r tr args)
          (match (parse-type param) args with
            type ()
            -> (oprintf "  %" (safe r) " = alloca " (ftypenv type) ", i32 1\n")
            _ _
            -> (imp)
            ))

        (define (add-rotate-decl t right?)
          (let ((ft (ftype t)))
            (cmap/add
             decls
             (format "declare " ft "@llvm.fsh" (if right? "r." "l.")
                     ft " (" ft ", " ft ", " ft ")"))))

        (define (prim-rotate right?)
          (lambda (param r tr args)
            (add-rotate-decl tr right?)
            (oprintf "  %" (safe r) " = call " (ftype tr) " @llvm."
                     (if right? "fshr" "fshl") "." (ftype tr) " ("
                     ;; first argument twice.
                     (join valreft ", " (list:cons (first args) args)) ")\n")))

        (define var->type
          (var:t _ type) -> (apply-subst type)
          )

        (define void?
          (type:none) -> #t
          _           -> #f
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
               -> (match (alist/lookup tenv name) with
                    (maybe:yes (type:arrow rtype argtypes))
                    -> (oprintf "  " (if (void? rtype) "" (format "%" (safe x) " = "))
                                "call " (ftype rtype) " @" (safe name)
                                " (" (join valreft ", " args) ")\n")
                    (maybe:yes ftype)
                    -> (raise (:LLVM/BadCallType (format (repr (type->sexp ftype)))))
                    (maybe:no)
                    -> (raise (:LLVM/NoSuchPrim (format (sym name))))
                    )
               )
          )

        (define faztname
          (aztname:t name type src)
          -> (format (ftype type) " %" (safe name))
          )

        (oprintf "define " (ftype rtype) " @" (safe name) " (" (join faztname ", " args) ") {\n")
        (oprintf "top:\n")
        (pass1 exp 'top)
        (emit exp 'top)
        (oprintf "}\n")
        )
      )

    (define (format-lit ty lit)
      (match ty lit with
        (type:none) (zlit:none)
        -> "void"
        (type:int size) (zlit:big n)
        -> (format (ftype ty) " " (big->dec n))
        (type:vec (itype:fix size) ty0) (zlit:vec subs)
        -> (if (= size (vector-length subs))
               (format "[" (int size) " x " (ftype ty0) "] ["
                       (join (partial (format-lit ty0 _)) ", " (vector->list subs)) "]")
               (raise (:BadLit lit)))
        ty vec
        -> (raise (:BadLit lit))
        ))

    ;; collect names of defined functions
    (for-list fun funs
      (match fun with
        (:tuple name _ _ _)
        -> (push! local name)
        ))
    (for-list lit lits
      (match lit with
        (:tuple name _ _)
        -> (push! local name)))
    ;; emit declarations first
    (for-alist name type tenv
      (when (not (member-eq? name local))
        (match type with
          (type:arrow rtype argtypes)
          -> (oprintf "declare " (ftype rtype) " @" (safe name) "(" (join ftype ", " argtypes) ")\n")
          _ ;; a literal
          -> (oprintf "declare " (ftype type) " @" (safe name) "\n")
          )))
    ;; emit lits
    (for-list lit (reverse lits)
      (match lit with
        (:tuple name (type:ref type) val)
        -> (oprintf "@" (safe name) " = constant " (format-lit type val) "\n")
        (:tuple name (type:mut type) val)
        -> (oprintf "@" (safe name) " = global " (format-lit type val) "\n")
        (:tuple name type other)
        -> (raise (:NotYetImplemented "non-ref top-level literals"))
        ))
    ;; emit functions
    (for-list fun funs
      (match fun with
        (:tuple name rtype formals cps)
        -> (cpsfun->llvm ofile tenv name rtype formals cps)
        ))
    ;; emit intrinsic decls
    (for-map k v decls.map
      (oprintf k "\n"))
    (file/flush ofile)
    (file/close ofile)
    0
    ))
