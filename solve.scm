;; -*- Mode: Irken -*-

;; type solving/checking

;; follow the links to the ultimate parent of this type.
(define (type-find t)
  (match t with
    (type:var n r)
    -> (match r.parent with
         (maybe:no)
         -> t
         (maybe:yes t0)
         -> (let ((p (type-find t0)))
              (set! r.parent (maybe:yes p))
              p)
         )
    t -> t
    ))

;; link through type variable
(define (type-union a b)
  (let ((pa (type-find a))
        (pb (type-find b)))
    (match pa pb with
      (type:var na ra) (type:var nb rb) -> (if (< na nb)
					       (set! rb.parent (maybe:yes pa))
					       (set! ra.parent (maybe:yes pb)))
      (type:var _ ra)  _                -> (set! ra.parent (maybe:yes pb))
      _                (type:var _ rb)  -> (set! rb.parent (maybe:yes pa))
      _ _ -> #u
      )))

(define (unify t0 t1)

  (define (type-error t0 t1)
    (let ((t0s (type->sexp t0))
          (t1s (type->sexp t1)))
      (printf "U " (sexp t0s) " != " (sexp t1s) "\n")
      (raise (:TypeError (:Unify t0s t1s)))
      ))

  ;; XXX I don't think we need this feature.
  ;; YYY now I think we do. (see `vref`).
  ;; ZZZ I think we want dependent types. maybe.
  (define U-int
    ;; allow t0 to unify with any other legit int.
    ;; [i.e. i0 acts like a type variable for integer size]
    (type:int 0) (type:int 0)   -> (type-error t0 t1)
    (type:int 0) (type:int nv)  -> #u
    (type:int nu) (type:int 0)  -> #u
    (type:int nu) (type:int nv) -> (if (= nu nv) #u (type-error t0 t1))
    _ _ -> (raise (:SayWhat?))
    )

  (define (U t0 t1)
    ;; (printf "U " (sexp (type->sexp t0)) " " (sexp (type->sexp t1)) "\n")
    (let ((u (type-find t0))
          (v (type-find t1)))
      (when (not (eq? u v))
        (match u v with
          (type:none) (type:none)
          -> #u
          (type:int nu) (type:int nv)
          -> (U-int u v)
          (type:vec nu tu) (type:vec nv tv)
          -> (if (= nu nv) (U tu tv) (type-error t0 t1))
          (type:arrow ru argsu) (type:arrow rv argsv)
          -> (begin (U ru rv) (for-each2 U argsu argsv))
          (type:ref tu) (type:ref tv)
          -> (U tu tv)
          (type:var _ _) _ -> #u
          _ (type:var _ _) -> #u
          _ _              -> (type-error t0 t1)
          )
        (type-union u v)
        )))

  (U t0 t1)
  )

(define (apply-subst t)
  (define (p t)
    (let ((t0 (type-find t)))
      (match t0 with
        (type:vec n vt)     -> (type:vec n (p vt))
        (type:arrow rt ats) -> (type:arrow (p rt) (map p ats))
        (type:ref rt)       -> (type:ref (p rt))
        _                   -> t0
        )))
  (p t))

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
  (repr (type->sexp t)))

;; verify all args are arith and the same. returns that type.
(define sig-prim-arith
  param rtype args
  -> (begin
       ;;(printf "U arith (" (join ftype ", " args) ") -> " (ftype rtype) "\n")
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
  _ _ _
  -> (raise (:TypeError (:NotRef)))
  )

(define sig-%get
  param rtype ((type:ref t0))
  -> (unify t0 rtype)
  param rtype ((type:mut t0))
  -> (unify t0 rtype)
  _ _ _
  -> (raise (:TypeError (:NotRef)))
  )

(define sig-vref
  param rtype ((type:ref (type:vec size t0)) tindex)
  -> (begin
       (unify tindex i0)
       (unify (type/ref t0) rtype)
       )
  _ a b
  -> (begin
       (printf "args = " (join (lambda (x) (repr (type->sexp x))) ", " b)  "\n")
       (raise (:TypeError (:Vref a b)))
       )
  )

;; this could be replaced with a `sig-conversion` that covered all the LLVM conversion
;;  operators including ptrtoint/inttoptr/fp/etc.
(define (sig-change-size bigger?)
  (lambda (param rtype args)
    (match args with
      ((type:int isize))
      -> (let ((ptype (parse-type param)))
           (match ptype with
             (type:int osize)
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

  (define (S env exp)
    ;;(printf "S:\n")
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
      -> (S env K) ;; probably not sufficient
      (cps:letcont (cvar:t k) xs K0 K1)
      -> (let ((env0 (alist:entry k (map var->type xs) env)))
           (S env0 K0) ;; note: k is defined in the init because loop.
           (S env0 K1))
      (cps:appk (cvar:t k) xs)
      -> (match (alist/lookup env k) with
           (maybe:yes txs)
           -> (for-list2 ta tb txs (map var->type xs)
                (unify ta tb))
           (maybe:no)
           -> (raise (:TypeError (:UnknownContinuation k))))
      (cps:app name k vars)
      -> (raise (:NotYetImplemented))
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

