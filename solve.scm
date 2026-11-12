;; -*- Mode: Irken -*-

;; type solving/checking

(define (ftype t)
  (type-repr (apply-subst t)))

;; assert that <t> is a vector type (as opposed to llvm array)
(define (vector-check env t)
  (match (apply-subst t) with
    (type:vec v? size base)
    -> (unify env t (type:vec (itype:fix 1) size base))
    _
    -> #u
    ))

;; verify all args are arith and the same. returns that type.
(define sig-prim-arith
  env param rtype args
  -> (begin
       (trace (printf "U arith (" (join ftype ", " args) ") -> " (ftype rtype) "\n"))
       (for-list arg args (unify env rtype arg))
       (vector-check env rtype)))

;; verify all args are arith and the same.  returns i1.
(define sig-prim-cmp
  env param rtype (targ0 targ1)
  -> (begin
       (unify env rtype i1)
       (unify env targ0 targ1)
       (vector-check env rtype)
       (vector-check env targ0))
  env param rtype targs
  -> (raise (:TypeError (:Arity targs)))
  )

(define sig-set!
  env param rtype ((type:mut t0) t1)
  -> (begin
       (unify env t0 t1)
       (unify env rtype none))
  _ _ _ argtypes
  -> (begin
       (printf "NotRef? (" (join type-repr ", " argtypes) ")\n")
       (raise (:TypeError (:NotRef)))
       )
  )

(define sig-%get
  env param rtype ((type:ref t0))
  -> (unify env t0 rtype)
  env param rtype ((type:mut t0))
  -> (unify env t0 rtype)
  ;; hack for non-ref vector %get.
  ;; param rtype (t0)
  ;; -> (unify env rtype t0)
  _ _ _ _
  -> (begin
       (printf "notref?\n")
       (raise (:TypeError (:NotRef)))
       )
  )

(define sig-vref
  env param rtype ((type:ref (type:vec v? size t0)) tindex)
  -> (begin
       (unify env tindex (type:int (new-itvar)))
       (unify env (type:ref t0) rtype)
       )
  env param rtype ((type:mut (type:vec v? size t0)) tindex)
  -> (begin
       (unify env tindex (type:int (new-itvar)))
       (unify env (type:mut t0) rtype)
       )
  env param rtype ((type:vec v? size t0) tindex)
  -> (begin
       (unify env tindex (type:int (new-itvar)))
       (unify env rtype t0)
       )
  env param a b
  -> (begin
       (printf "param = " (repr param) "\n")
       (printf "args = " (join (lambda (x) (repr (type->sexp x))) ", " b)  "\n")
       (raise (:TypeError (:Vref a b)))
       )
  )

;; this could be replaced with a `sig-conversion` that covered all the LLVM conversion
;;  operators including ptrtoint/inttoptr/fp/etc.
(define (sig-change-size bigger?)
  (lambda (env param rtype args)
    (match args with
      ((type:int (itype:fix isize)))
      -> (let ((ptype (parse-type param)))
           (match ptype with
             (type:int (itype:fix osize))
             -> (if ((if bigger? > <) osize isize)
                    (unify env rtype ptype)
                    (raise (:TypeError (:Zext isize osize))))
             _
             -> (begin
                  (printf "parsed " (repr param) " as " (repr (type->sexp ptype)) "\n")
                  (raise (:TypeError (:BadType ptype)))
                  )
             ))
      (itype)
      -> (raise (:TypeError (:BadType itype)))
      args
      -> (raise (:TypeError (:Arity args)))
      )))

;; XXX removing type param.
;; (prim alloca i64) => i64*

(define sig-alloca
  env param rtype ()
  -> #u
  ;; -> (let ((ptype (parse-type param)))
  ;;      (unify env rtype (type:mut ptype)))
  env param rtype argtypes
  -> (raise (:TypeError (:Arity argtypes)))
  )

;; v0 and v1 are the same vector type/size
;; m is a vector of i32
;; rtype is a vector |m| with type of v0/v1 elems.
(define sig-shufv
  env param rtype (v0 v1 m)
  -> (let ((item-type (new-tvar))
           (mask-size (new-itvar)))
       (unify env v0 (type:vec btype-true (new-itvar) item-type))
       (unify env v0 v1)
       (unify env m (type:vec btype-true mask-size i32))
       (unify env rtype (type:vec btype-true mask-size item-type))
       )
  env param rtype (v0 m)
  -> (let ((item-type (new-tvar))
           (mask-size (new-itvar)))
       (unify env v0 (type:vec btype-true (new-itvar) item-type))
       (unify env m (type:vec btype-true mask-size i32))
       (unify env rtype (type:vec btype-true mask-size item-type))
       )
  _ _ _ _
  -> (raise (:TypeError (:BadArgs "shuffle")))
  )

(define sig-print
  env param rtype (arg)
  -> (unify env rtype none)
  _ _ _ _
  -> (raise (:TypeError (:BadArgs "print")))
  )

(define prim-type-map
  (alist/make
   ('+     sig-prim-arith)
   ('-     sig-prim-arith)
   ('*     sig-prim-arith)
   ('/     sig-prim-arith)
   ('mod   sig-prim-arith)
   ('and   sig-prim-arith)
   ('or    sig-prim-arith)
   ('xor   sig-prim-arith)
   ('<<    sig-prim-arith)
   ('>>    sig-prim-arith)
   ('ashr  sig-prim-arith)
   ('<<<   sig-prim-arith)
   ('>>>   sig-prim-arith)
   ('=     sig-prim-cmp)
   ('<>    sig-prim-cmp)
   ('<     sig-prim-cmp)
   ('>     sig-prim-cmp)
   ('<=    sig-prim-cmp)
   ('>=    sig-prim-cmp)
   ('%set! sig-set!)
   ('%vref sig-vref)
   ('%get  sig-%get)
   ('zext  (sig-change-size #t))
   ('trunc (sig-change-size #f))
   ('alloca sig-alloca)
   ('shufv sig-shufv)
   ('print sig-print)
   ))

;; solve types for a CPS exp

(define (solve tenv cenv exp)

  (define (UK env k0 k1)
    ;; (printf "UK\n")
    (match (alist/lookup env k0) (alist/lookup env k1) with
      (maybe:yes txs) (maybe:yes tys)
      -> (for-list2 tx ty txs tys
           (unify env tx ty))
      _ _
      -> (raise (:TypeError (:UnknownContinuations k0 k1)))
      ))

  (define var->type
    (var:t x tx) -> (apply-subst tx)
    )

  (define fvart
    (var:t x tx) -> (format (sym x) ":" (type-repr tx))
    )

  ;; identical to the one in solve-zexp.
  (define Slit
    env ty (zlit:none)
    -> (unify env ty (type:none))
    env ty (zlit:big n)
    -> (unify env ty (type:int (new-itvar)))
    env ty (zlit:vec lits)
    -> (let ((tv (new-tvar))
             (tsz (itype:fix (vector-length lits))))
         (trace (printf "Slit vec ty=" (type-repr ty) " tsz=" (repr (itype->sexp tsz)) "\n"))
         (unify env ty (type:vec (new-itvar) tsz tv)) ;; XXX bvar
         (for-vector lit lits
           (trace (printf "each lit\n"))
           (Slit env tv lit))))

  (define (S env exp)
    (trace (printf "S:\n"))
    (match exp with
      (cps:prim name param (var:t x tx) xs K)
      -> (begin
           (trace (printf "S prim " (sym name) " " (repr param) " " (sym x) ":" (repr (type->sexp tx))
                   " (" (join fvart " " xs) ")\n"))
         (match (alist/lookup prim-type-map name) with
           (maybe:yes fun)
           -> (let ((txs (map var->type xs)))
                ;; XXX empty env kludge: `env` here maps continuations to
                ;;  (list type), but the prim sigs are shared with solve-zexp,
                ;;  whose env maps names to types.  (unify ignores it so far.)
                (fun (alist:nil) param tx txs)
                (S env K))
           (maybe:no)
           -> (match (alist/lookup tenv name) with
                (maybe:yes (type:arrow rtype argtypes))
                -> (let ((txs (map var->type xs)))
                     (for-list2 a b txs (map undyn-type argtypes)
                       (unify env a b))
                     (unify env rtype tx)
                     (S env K))
                _
                -> (raise (:TypeError (:UnknownPrim name)))
                )))
      (cps:letval (var:t x tx) val K)
      -> (begin
           (trace (printf "Slit " (type-repr tx) " ==? " (zlit-repr val) "\n"))
           (Slit env tx val)
           (S env K))
      (cps:letcont (cvar:t k) xs K0 K1)
      -> (let ((env0 (alist:entry k (map var->type xs) env)))
           ;; (printf "S letcont " (sym k) " (" (join fvart " " xs) ")\n")
           (S env0 K0) ;; note: k is defined in the init because loop.
           (S env0 K1))
      (cps:appk (cvar:t k) xs)
      -> (match (alist/lookup env k) with
           (maybe:yes txs)
           -> (for-list2 ta tb txs (map var->type xs)
                ;; (printf "appk arg " (type-repr ta) " = " (type-repr tb) "\n")
                (unify env ta tb))
           (maybe:no)
           -> (raise (:TypeError (:UnknownContinuation k))))
      (cps:app name k vars)
      -> (raise (:NotYetImplemented "internal funcall"))
      (cps:if (var:t t tt) (cvar:t c) (cvar:t a))
      -> (begin
           (unify env tt i1)
           (UK env c a))
      (cps:dead k)
      -> (S env k)
      ))
  (S cenv exp)
  )

;; apply-subst recursively over a typed cps expression.
(define (cps-subst exp)
  (define Av
    (var:t x tx) -> (var:t x (apply-subst tx))
    )
  (define A
    (cps:prim name p x xs K) -> (cps:prim name p (Av x) (map Av xs) (A K))
    (cps:letval x val K)     -> (cps:letval (Av x) val (A K))
    (cps:letcont k xs K0 K1) -> (cps:letcont k (map Av xs) (A K0) (A K1))
    (cps:appk k xs)          -> (cps:appk k (map Av xs))
    (cps:app name k xs)      -> (cps:app name k (map Av xs))
    (cps:if x k0 k1)         -> (cps:if (Av x) k0 k1)
    (cps:dead K)             -> (cps:dead (A K))
    )
  (A exp)
  )

;; remove void continuation arguments.
(define (strip-void exp)
  (define non-void?
    (var:t _ (type:none)) -> #f
    _                     -> #t
    )
  (define (F xs) (filter non-void? xs))
  (define S
    (cps:prim name p x vars K) -> (cps:prim name p x vars (S K))
    (cps:letval x V K)         -> (cps:letval x V (S K))
    (cps:letcont k xs K L)     -> (cps:letcont k (F xs) (S K) (S L))
    (cps:appk k xs)            -> (cps:appk k (F xs))
    (cps:dead K)               -> (cps:dead (S K))
    otherwise                  -> otherwise
    )
  (S exp)
  )

;; provide a default (e.g. i32) for otherwise unknown array indexing.
(define (default-vec-index exp index-type)

  (define W
    (cps:prim '%vref _ _ (src (var:t i ti)) K)
    -> (match (apply-subst ti) with
         (type:int (itype:var _))
         ;; XXX empty env kludge
         -> (begin (unify (alist:nil) ti index-type) (W K))
         _
         -> (W K)
         )
    (cps:prim _ _ _ _ K)   -> (W K)
    (cps:letval x V K)     -> (W K)
    (cps:letcont k xs K L) -> (begin (W K) (W L))
    (cps:dead K)           -> (W K)
    otherwise              -> #u
    )

  (W exp)

  )

;; --- itype:dyn vector arguments ---
;;
;; the type signature makes a statement about the size of an argument vector being equal to
;;   another argument's _value_.  How can we verify this at the call site?  For example,
;;   what if two length arguments have their names swapped?  At the point of call, we don't
;;   know what name it was probably pulled from as a varref.  However, we _do_ know that
;;   since everything has typed up to this point, that the vectors are properly typed at
;;   this time.  I think handling this 'swap of len args' error is our 'proof of
;;   principle': if we can do it, then this idea is valid.  If not, then no.
;;
;; for example, does our idea allow the computation of such a length?  e.g., what if we
;;   want to pass in `a` that is twice the size of `b`?  I think the only way to do that
;;   within our type system is to have the 'twice the size' value be in a variable, and the
;;   type of the larger vec must be built on that variable.

;; my current thinking: we can verify the proper arguments in a zexp pass.
;;   in the meanwhile to get this to type we need to replace itype:dyn with itype:var.

;; if a funcall is made that passes a itype:dyn vector, replace
;; the itype:dyn with an itype:var.
(define (undyn-type t)
  (define I
    (itype:dyn n) -> (new-itvar)
    t             -> t
    )
  (define T
    (type:vec v? size base) -> (type:vec (I v?) (I size) (T base))
    (type:mut t)            -> (type:mut (T t))
    (type:ref t)            -> (type:ref (T t))
    (type:arrow rt ts)      -> (type:arrow (T rt) (map T ts))
    t                       -> t
    )
  (T t)
  )

;; solve types for zexp

(define (solve-zexp tenv exp)

  (define zexp->kind (ob->dtarm 'zexp))

  (define (extend-with-cont env kname binds)
    (define R
      env0 txs ()
      -> (:tuple env0 txs)
      env0 txs ((:tuple (aztname:t name type _) exp) . tl)
      -> (begin
           (S env type exp) ;; NB: not the currently-being-extend env.
           (R (alist:entry name type env0) (list:cons type txs) tl))
      )
    (let (((env0 types) (R env '() binds)))
      (alist:entry
       kname
       (type:arrow (type:none) (reverse types))
       env0)))

  (define (extend-formals env formals)
    (define R
      env0 txs ()
      -> (:tuple env0 txs)
      env0 txs ((aztname:t name type _) . tl)
      -> (R (alist:entry name type env0) (list:cons type txs) tl))
    (R env '() formals))

  (define Slit
    env ty (zlit:none)
    -> (unify env ty (type:none))
    env ty (zlit:big n)
    -> (unify env ty (type:int (new-itvar)))
    env ty (zlit:vec lits)
    -> (let ((tv (new-tvar))
             (tsz (itype:fix (vector-length lits))))
         (unify env ty (type:vec (new-itvar) tsz tv))
         (for-vector lit lits
           (Slit env tv lit))))

  (define (type-repr* t)
    (type-repr (apply-subst t)))

  (define (exp->type exp)
    (apply-subst (azexp/type exp)))

  (define (Sprim env ty name param xs)
    (trace (printf "Sprim " (sym name) " " (repr param) " " (type-repr* ty)
            " (" (join type-repr* " " (map exp->type xs)) ")\n"))
    (match (alist/lookup prim-type-map name) with
      (maybe:yes fun)
      -> (begin
           ;; (printf "unifying prim args...\n")
           (for-list x xs
             (S env (exp->type x) x))
           ;; (printf "calling sig fun...\n")
           ;; (printf "  " (type-repr* ty) " = (" (join type-repr* " " (map exp->type xs)) ")\n")
           (fun env param ty (map exp->type xs)))
      (maybe:no)
      -> (match (alist/lookup env name) with
           (maybe:yes funtype)
           -> (Scall env ty funtype xs)
           _
           -> (raise (:TypeError (:UnknownPrim name)))
           )))

  (define (Scall env ty funtype args)
    (match funtype with
      (type:arrow rtype argtypes)
      -> (begin
           ;; XXX we need to 'instantiate' ftype's formals-vs-args
           (trace (printf "Scall targ " (ftype rtype) " args " (join ftype ", " argtypes) "\n"))
           (for-list2 arg targ args (map undyn-type argtypes)
             (trace (printf "  arg " (ftype targ) "\n"))
             (S env targ arg))
           (unify env ty rtype))
      _
      -> (raise (:TypeError (:FunCall (type-repr funtype))))
      ))

  (define S
    env ty0 (azexp:t exp src ty1)
    -> (begin
         (trace (printf "S " (sym (zexp->kind exp)) "\n"))
         (unify env ty0 ty1)
         (S* env ty0 exp))
    )

  (define S*

    env ty (zexp:lit lit)
    -> (Slit env ty lit)

    env ty (zexp:prim name param args)
    -> (Sprim env ty name param args)

    env ty (zexp:seq subs)
    -> (let loop ((subs subs))
         (match subs with
           ()        -> #u ;; not reached
           (last)    -> (S env ty last) ;; return type of seq
           (hd . tl) -> (begin (S env (new-tvar) hd) (loop tl))
           ))

    env ty (zexp:let (aztname:t name type src) init body)
    -> (let ((env0 (alist:entry name type env)))
         (S env type init)
         (S env0 ty body))

    env ty (zexp:varref name)
    -> (match (alist/lookup env name) with
         (maybe:yes ty1) -> (unify env ty ty1)
         (maybe:no)      -> (begin
                              (printf "varref of " (sym name) "\n")
                              (impossible)
                              )
         )

    env ty (zexp:if tst con alt)
    -> (begin
         (S env i1 tst)
         (S env ty con)
         (S env ty alt))

    env ty (zexp:call name args)
    -> (match (alist/lookup env name) with
         (maybe:yes ftype)
         -> (Scall env ty ftype args)
         _
         -> (raise (:TypeError (:BadCall name))))

    env ty (zexp:loop name binds body)
    -> (let ((env0 (extend-with-cont env name binds)))
         (S env0 ty body))

    env ty (zexp:letcont name formals K L)
    -> (let (((env0 ftys) (extend-formals env formals)) ;; extended with vars
             (env1 (alist:entry name (type:arrow (type:none) ftys) env))) ;; with cont.
         (S env0 ty K)
         (S env1 ty L))

    env ty (zexp:appk name args)
    -> (match (alist/lookup env name) with
         (maybe:yes (type:arrow _ formals))
         -> (for-list2 arg targ args formals
              (S env targ arg))
         _
         -> (impossible)
         )

    )

  (S tenv (new-tvar) exp)

  )

