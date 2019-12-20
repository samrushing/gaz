;; -*- Mode: Irken -*-

;; type solving/checking

(define (type=? ta tb)
  (magic=? ta tb))

;; is this type suitable for arithmetic ops?
(define arith?
  (type:int _)              -> #t
  (type:vec _ (type:int _)) -> #t
  _                         -> #f
  )

;; NOTE: these schemes don't capture the need for int/vec types.
;;
;; to think about: the solver might want to be more like irken's,
;;  with a generic pred/tvar system.  could we extend it with an
;;  'int' arm, like this: (ref (int 'a)) which could assign an integer
;;  size to 'a??  Urgh, nope: then we could have (ref 3).  can this
;;  be solved with types at all?  Or do we just punt and throw the
;;  error during LLVM conversion?  Or make a second 'type-sanity' pass?
;; OR am I just over-thinking all of this and using simple functions
;;  to do the type solving will work fine?

(define (ftype t)
  (type-repr (apply-subst t)))

;; verify all args are arith and the same. returns that type.
(define sig-prim-arith
  param rtype args
  -> (begin
       ;; (printf "U arith (" (join ftype ", " args) ") -> " (ftype rtype) "\n")
       (for-list arg args (unify rtype arg)))
  )

;; verify all args are arith and the same.  returns i1.
(define sig-prim-cmp
  param rtype (targ0 targ1)
  -> (begin (unify rtype i1) (unify targ0 targ1))
  param rtype targs
  -> (raise (:TypeError (:Arity targs)))
  )

(define sig-set!
  param rtype ((type:mut t0) t1)
  -> (begin
       (unify t0 t1)
       (unify rtype none))
  _ _ argtypes
  -> (begin
       (printf "NotRef? (" (join type-repr ", " argtypes) ")\n")
       (raise (:TypeError (:NotRef)))
       )
  )

(define sig-%get
  param rtype ((type:ref t0))
  -> (unify t0 rtype)
  param rtype ((type:mut t0))
  -> (unify t0 rtype)
  ;; hack for non-ref vector %get.
  ;; param rtype (t0)
  ;; -> (unify rtype t0)
  _ _ _
  -> (begin
       (printf "notref?\n")
       (raise (:TypeError (:NotRef)))
       )
  )

(define sig-vref
  param rtype ((type:ref (type:vec size t0)) tindex)
  -> (begin
       ;; we want to express that tindex is an integer type, but
       ;;  there's no way to do that now.  The i0 hack does not work.
       ;;(unify tindex (type:int 0))
       (unify tindex (type:int (new-itvar)))
       (unify (type:ref t0) rtype)
       )
  param rtype ((type:mut (type:vec size t0)) tindex)
  -> (begin
       (unify tindex (type:int (new-itvar)))
       (unify (type:mut t0) rtype)
       )
  param rtype ((type:vec size t0) tindex)
  -> (begin
       (unify tindex (type:int (new-itvar)))
       (unify rtype t0)
       )
  param a b
  -> (begin
       (printf "param = " (repr param) "\n")
       (printf "args = " (join (lambda (x) (repr (type->sexp x))) ", " b)  "\n")
       (raise (:TypeError (:Vref a b)))
       )
  )

;; this could be replaced with a `sig-conversion` that covered all the LLVM conversion
;;  operators including ptrtoint/inttoptr/fp/etc.
(define (sig-change-size bigger?)
  (lambda (param rtype args)
    (match args with
      ((type:int (itype:fix isize)))
      -> (let ((ptype (parse-type param)))
           (match ptype with
             (type:int (itype:fix osize))
             -> (if ((if bigger? > <) osize isize)
                    (unify rtype ptype)
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

;; (prim alloca i64) => i64*

(define sig-alloca
  param rtype ()
  -> (let ((ptype (parse-type param)))
       (unify rtype (type:mut ptype)))
  ;; XXX probably not
  param rtype (n)
  -> (let ((ptype (parse-type param)))
       (unify rtype (type:mut ptype))
       (unify n i32))
  param rtype argtypes
  -> (raise (:TypeError (:Arity argtypes)))
  )

(define prim-type-map
  (alist/make
   ('+     sig-prim-arith)
   ('-     sig-prim-arith)
   ('*     sig-prim-arith)
   ('/     sig-prim-arith)
   ('rem   sig-prim-arith)
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
   ))

;; solve types for a CPS exp

(define (solve tenv cenv exp)

  (define (UK env k0 k1)
    ;; (printf "UK\n")
    (match (alist/lookup env k0) (alist/lookup env k1) with
      (maybe:yes txs) (maybe:yes tys)
      -> (for-list2 tx ty txs tys
           (unify tx ty))
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
    ty (zlit:none)
    -> (unify ty (type:none))
    ty (zlit:big n)
    -> (unify ty (type:int (new-itvar)))
    ty (zlit:vec lits)
    -> (let ((tv (new-tvar))
             (tsz (itype:fix (vector-length lits))))
         (printf "Slit vec ty=" (type-repr ty) " tsz=" (repr (itype->sexp tsz)) "\n")
         (unify ty (type:vec tsz tv))
         (for-vector lit lits
           (printf "each lit\n")
           (Slit tv lit))))

  (define (S env exp)
    (printf "S:\n")
    (match exp with
      (cps:prim name param (var:t x tx) xs K)
      -> (begin
           (printf "S prim " (sym name) " " (repr param) " " (sym x) ":" (repr (type->sexp tx))
                   " (" (join fvart " " xs) ")\n")
         (match (alist/lookup prim-type-map name) with
           (maybe:yes fun)
           -> (let ((txs (map var->type xs)))
                (fun param tx txs)
                (S env K))
           (maybe:no)
           -> (match (alist/lookup tenv name) with
                (maybe:yes (type:arrow rtype argtypes))
                -> (let ((txs (map var->type xs)))
                     (for-list2 a b txs argtypes
                       (unify a b))
                     (unify rtype tx)
                     (S env K))
                _
                -> (raise (:TypeError (:UnknownPrim name)))
                )))
      (cps:letval (var:t x tx) val K)
      -> (begin
           (printf "Slit " (type-repr tx) " ==? " (zlit-repr val) "\n")
           (Slit tx val)
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
                (unify ta tb))
           (maybe:no)
           -> (raise (:TypeError (:UnknownContinuation k))))
      (cps:app name k vars)
      -> (raise (:NotYetImplemented "internal funcall"))
      (cps:if (var:t t tt) (cvar:t c) (cvar:t a))
      -> (begin
           (unify tt i1)
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
    (cps:prim '%vref _ _ (src index) K)
    -> (match index with
         (var:t _ (type:int (itype:var _)))
         -> (begin (unify (var/type index) index-type) (W K))
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


;; solve types for zexp

(define (solve-zexp tenv exp)

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
    ty (zlit:none)
    -> (unify ty (type:none))
    ty (zlit:big n)
    -> (unify ty (type:int (new-itvar)))
    ty (zlit:vec lits)
    -> (let ((tv (new-tvar))
             (tsz (itype:fix (vector-length lits))))
         (unify ty (type:vec tsz tv))
         (for-vector lit lits
           (Slit tv lit))))

  (define (type-repr* t)
    (type-repr (apply-subst t)))

  (define (exp->type exp)
    (apply-subst (azexp/type exp)))

  (define (Sprim env ty name param xs)
    ;; (printf "Sprim " (sym name) " " (repr param) " " (type-repr* ty)
    ;;         " (" (join type-repr* " " (map exp->type xs)) ")\n")
    (match (alist/lookup prim-type-map name) with
      (maybe:yes fun)
      -> (begin
           ;; (printf "unifying prim args...\n")
           (for-list x xs
             (S env (exp->type x) x))
           ;; (printf "calling sig fun...\n")
           ;; (printf "  " (type-repr* ty) " = (" (join type-repr* " " (map exp->type xs)) ")\n")
           (fun param ty (map exp->type xs)))
      (maybe:no)
      -> (match (alist/lookup env name) with
           (maybe:yes (type:arrow rtype argtypes))
           -> (let ((txs (map exp->type xs)))
                (for-list2 a b txs argtypes
                  (unify a b))
                (unify rtype ty))
           _
           -> (raise (:TypeError (:UnknownPrim name)))
           )))

  (define S
    env ty0 (azexp:t exp src ty1)
    -> (begin
         (unify ty0 ty1)
         ;; (printf "S* " (sym (zname exp)) "\n")
         (S* env ty0 exp))
    )

  (define zname
    (zexp:lit _)           -> 'lit
    (zexp:prim _ _ _)      -> 'prim
    (zexp:seq _)           -> 'seq
    (zexp:let _ _ _)       -> 'let
    (zexp:varref _)        -> 'varref
    (zexp:if _ _ _)        -> 'if
    (zexp:call _ _)        -> 'call
    (zexp:loop _ _ _)      -> 'loop
    (zexp:letcont _ _ _ _) -> 'letcont
    (zexp:appk _ _)        -> 'appk
    )

  (define S*

    env ty (zexp:lit lit)
    -> (Slit ty lit)

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
         (maybe:yes ty1) -> (unify ty ty1)
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
         (maybe:yes (type:arrow rtype argtypes))
         -> (begin
              (for-list2 arg targ args argtypes
                (S env targ arg))
              (unify ty rtype))
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

