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

