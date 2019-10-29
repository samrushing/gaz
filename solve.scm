;; -*- Mode: Irken -*-

;; type solving/checking

(define (type=? ta tb)
  (magic=? ta tb))

;; is this type suitable for arithmetic ops?
(define arith?
  (type:int _ _)                -> #t
  (type:vec _ (type:int _ _) _) -> #t
  _                             -> #f
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
  rtype args
  -> (begin
       (printf "U prim " (join ftype ", " args) " -> " (ftype rtype) "\n")
       (for-list arg args (unify rtype arg)))
  )

;; verify all args are arith and the same.  returns i1.
(define sig-prim-cmp
  rtype (targ0 targ1)
  -> (begin (unify rtype i1) (unify targ0 targ1))
  rtype targs
  -> (raise (:TypeError (:Arity targs)))
  )

(define sig-set!
  rtype ((type:ref t0 _) t1)
  -> (begin
       (unify t0 t1)
       (unify rtype none))
  _ _
  -> (raise (:TypeError (:NotRef )))
  )

(define prim-type-map
  (alist/make
   ('+     sig-prim-arith)
   ('-     sig-prim-arith)
   ('*     sig-prim-arith)
   ('/     sig-prim-arith)
   ('and   sig-prim-arith)
   ('or    sig-prim-arith)
   ('xor   sig-prim-arith)
   ('<<    sig-prim-arith)
   ('>>    sig-prim-arith)
   ('ashr  sig-prim-arith)
   ('=     sig-prim-cmp)
   ('<>    sig-prim-cmp)
   ('<     sig-prim-cmp)
   ('>     sig-prim-cmp)
   ('<=    sig-prim-cmp)
   ('>=    sig-prim-cmp)
   ('set!  sig-set!)
   ))

;; XXX consider rewriting <exp> with solved types, rather than
;;   requiring users to apply-subst at all types.
(define (solve tenv env exp)

  (define (UK k0 k1)
    (match (alist/lookup env k0) (alist/lookup env k1) with
      (maybe:yes txs) (maybe:yes tys)
      -> (for-list2 tx ty txs tys
           (unify tx ty))
      _ _
      -> (raise (:TypeError (:UnknownContinuations k0 k1)))
      ))

  (define (S env exp)
    (match exp with
      (cps:prim name (var:t x tx) xs K)
      -> (match (alist/lookup prim-type-map name) with
           (maybe:yes fun)
           -> (let ((txs (map var/type xs)))
                (fun tx txs)
                (S env K))
           (maybe:no)
           -> (match (alist/lookup tenv name) with
                (maybe:yes (type:arrow rtype argtypes _))
                -> (let ((txs (map var/type xs)))
                     (for-list2 a b txs argtypes
                       (unify a b))
                     (unify rtype tx)
                     (S env K))
                _
                -> (raise (:TypeError (:UnknownPrim name)))))
      (cps:letval (var:t x tx) val K)
      -> (S env K) ;; probably not sufficient
      (cps:letcont (cvar:t k) xs K0 K1)
      -> (let ((env0 (alist:entry k (map var/type xs) env)))
           (S env0 K0) ;; note: k is defined in the init because loop.
           (S env0 K1))
      (cps:appk (cvar:t k) xs)
      -> (match (alist/lookup env k) with
           (maybe:yes txs)
           -> (for-list2 ta tb txs (map var/type xs)
                (unify ta tb))
           (maybe:no)
           -> (begin
                (printn env)
                (raise (:TypeError (:UnknownContinuation k)))))
      (cps:app name k vars)
      -> (raise (:NotYetImplemented))
      (cps:if (var:t t tt) (cvar:t c) (cvar:t a))
      -> (begin
           (unify tt i1)
           (UK c a))
      (cps:dead k)
      -> (S env k)
      ))
  (S env exp)
  )
