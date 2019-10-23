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

;; verify all args are arith and the same. returns that type.
(define sig-prim-arith
  rtype args
  -> (for-list arg args
       (unify rtype arg))
  )

;; verify all args are arith and the same.  returns i1.
(define sig-prim-cmp
  rtype (arg0 arg1)
  -> (begin (unify rtype i1) (unify arg0 arg1))
  rtype args
  -> (raise (:TypeError (:Arity args)))
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
   ))

(define solve
  cenv (cps:prim name (var:t x tx) xs K)
  -> (match (alist/lookup prim-type-map name) with
       (maybe:yes fun)
       -> (let ((txs (map var/type xs)))
            (fun tx txs)
            (solve cenv K))
       (maybe:no)
       -> (raise (:TypeError (:UnknownPrim name))))
  cenv (cps:letval (var:t x tx) val K)
  -> (solve cenv K) ;; probably not sufficient
  cenv (cps:letcont (cvar:t k tk) xs K0 K1)
  -> (let ((cenv0 (alist:entry k (map var/type xs) cenv)))
       (solve cenv0 K0) ;; note: k is defined in the init because loop.
       (solve cenv0 K1)
       ;; XXX what about `tk`??
       )
  cenv (cps:appk (cvar:t k tk) xs)
  -> (match (alist/lookup cenv k) with
       (maybe:yes txs)
       -> (for-list2 ta tb txs (map var/type xs)
            (unify ta tb)
            ;; XXX what about `tk`??
            )
       (maybe:no)
       -> (begin
            (printn cenv)
            (raise (:TypeError (:UnknownContinuation k)))
            )
       )
  cenv (cps:app name k vars)
  -> (raise (:NotYetImplemented))
  cenv (cps:if (var:t t tt) (cvar:t c tc) (cvar:t a ta))
  -> (begin
       (unify tt i1)
       (unify tc ta))
  cenv (cps:dead k)
  -> (solve cenv k)
  )





