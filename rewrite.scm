;; -*- Mode: Irken -*-

;; See Fig 5 in CwCC

(define (cps-repr cps)
  (repr (cps->sexp cps)))

;; this is over-complicated by the var/cvar distinction.

(define (make-census cmpfun)
  (let ((census (tree/empty)))
    (define (add key)
      (match (tree/member census cmpfun key) with
        (maybe:yes val) -> (inc! val.count)
        (maybe:no) -> (tree/insert! census cmpfun key {count=1})
        ))
    (define (get key)
      (match (tree/member census cmpfun key) with
        (maybe:yes val) -> val.count
        (maybe:no) -> 0
        ))
    (define (dump fkey)
      (for-map k v census
        (printf (lpad 15 (fkey k)) " : " (lpad 5 (int v.count)) "\n"))
      )
    (define (clear)
      (set! census (tree/empty)))
    {add=add get=get dump=dump clear=clear}
    ))

(define cmp-var
  (var:t a _) (var:t b _) -> (symbol-index-cmp a b)
  )
(define cmp-cvar
  (cvar:t a) (cvar:t b) -> (symbol-index-cmp a b)
  )

;; XXX HACK
(define type-apply-subst apply-subst)

(define (rewrite-cps exp)

  (let ((vcount (make-census cmp-var))  ;; variable/function usage counts
        (ccount (make-census cmp-cvar)) ;; continuation usage by if.
        (acount (make-census cmp-cvar)) ;; continuation usage by appk.
        (nopt 0)) ;; count of simplifications in the current pass.

    (define census/take
      (cps:letval x v t)       -> (census/take t)
      (cps:letcont k xs t0 t1) -> (begin (census/take t0) (census/take t1))
      (cps:appk k xs)          -> (begin (acount.add k) (for-each vcount.add xs))
      (cps:app f k args)       -> (begin (ccount.add k) (for-each vcount.add args))
      (cps:prim n p x args t)  -> (begin (for-each vcount.add args) (census/take t))
      (cps:if x k0 k1)         -> (begin (vcount.add x) (ccount.add k0) (ccount.add k1))
      (cps:dead K)             -> (census/take K)
      )

    (define (apply-subst S cmp x)
      (match (tree/member S cmp x) with
	(maybe:no)    -> x
	(maybe:yes y) -> y
	))

    (define fvar  (var:t name _) -> (format (sym name)))
    (define fcvar (cvar:t name)  -> (format (sym name)))

    (define vars-eq?
      () ()               -> #t
      (h0 . t0) (h1 . t1) -> (if (eq? h0 h1) (vars-eq? t0 t1) #f)
      a b                 -> #f
      )

    (define var-cmp (var:t a _) (var:t b _) -> (symbol-index-cmp a b))
    (define cvar-cmp (cvar:t a) (cvar:t b) -> (symbol-index-cmp a b))
    (define apply-vsubst (:tuple Sv Sk) x -> (apply-subst Sv var-cmp x))
    (define apply-csubst (:tuple Sv Sk) k -> (apply-subst Sk cvar-cmp k))
    (define extend-vsubst (:tuple Sv Sk) k v -> (:tuple (tree/insert Sv var-cmp k v) Sk))
    (define extend-csubst (:tuple Sv Sk) k v -> (:tuple Sv (tree/insert Sk cvar-cmp k v)))
    (define (extend-vsubst* S ks vs)
      (match ks vs with
        () ()
        -> S
        (k0 . ks) (v0 . vs)
        -> (extend-vsubst* (extend-vsubst S k0 v0) ks vs)
        _ _
        -> (raise (:BadArity ks vs))
        ))

    (define extend-venv (var:t k _) v env -> (alist:entry k v env))
    (define extend-cenv (cvar:t k) v env -> (alist:entry k v env))
    (define lookup-venv (var:t k _) env -> (alist/lookup env k))
    (define lookup-cenv (cvar:t k) env -> (alist/lookup env k))

    (define (substitute-vars subst exp)

      (define (S x)
        (match (apply-vsubst subst x) with
          (var:t name type)
          -> (var:t name (T (type-apply-subst type)))
          ))

      (define TI
        (itype:dyn name)
        -> (match subst with
             (:tuple Sv Sk)
             -> (match (tree/member Sv var-cmp (var:t name none)) with
                  (maybe:yes (var:t name0 type0))
                  -> (begin
                       (trace (printf "replacing name " (sym name) " with " (sym name0) "\n"))
                       (itype:dyn name0))
                  _ -> (itype:dyn name)
                  ))
        ;; -> (match (apply-vsubst subst (var:t name none)) with
        ;;      (var:t name0 type0)
        ;;      -> (begin
        ;;           (printf "replacing name " (sym name) " with " (sym name0) "\n")
        ;;           (itype:dyn name0)
        ;;           )
        ;;      )
        t -> t
        )

      (define T*
        (type:vec v? size base) -> (type:vec (TI v?) (TI size) (T base))
        (type:arrow rt txs)     -> (type:arrow (T rt) (map T txs))
        (type:ref t)            -> (type:ref (T t))
        (type:mut t)            -> (type:mut (T t))
        t                       -> t
        )

      (define (T t)
        (let ((t0 (T* t)))
          (trace (printf (ansi red " --- ") (ftype t) " => " (ftype t0) "\n"))
          t0))

      (define R
        (cps:prim n p x vars k)  -> (cps:prim n p (S x) (map S vars) (R k))
        (cps:letval x v k)       -> (cps:letval (S x) v (R k))
        (cps:letcont k xs t0 t1) -> (cps:letcont k (map S xs) (R t0) (R t1))
        (cps:appk k xs)          -> (cps:appk k (map S xs))
        (cps:app n k vars)       -> (cps:app n k (map S vars))
        (cps:if tst c a)         -> (cps:if (S tst) c a)
        (cps:dead k)             -> (cps:dead (R k))
        )
      (R exp))

    (define (simp venv cenv S K)

      (define (N s e)
	;; notify that a pass has a hit
        (inc! nopt)
        (trace (printf "N " (sym s) "\n"))
	;; (printf (sym s) " " (cps-repr K) "\n")
	;; (printf "  : " (cps-repr e) "\n")
	e)

      (define can-eta-cont?
        (cps:appk k xs) ys
        -> (if (vars-eq? (map subst/v xs) (map subst/v ys))
               (maybe:yes (subst/k k))
               (maybe:no))
        _ _
        -> (maybe:no)
        )

      (define (subst/v x)
        (apply-vsubst S x))

      (define (subst/k k)
        (apply-csubst S k))

      (match K with
	;; DEAD-VAL
	(cps:letval x V L)
	-> (if (= (vcount.get x) 0) ;;; XXXXX disabled by use of '<'
	       (N 'dead-val (simp venv cenv S L))
	       (let ((x0 (apply-vsubst S x)))
		 (cps:letval x0 V (simp (extend-venv x0 V venv) cenv S L))))
        ;; DEAD-PRIM cps:prim also binds a value
        ;; ===================================================================
        ;; XXX need to know when a prim is for side-effect only, can we check
        ;;   for dead continuation?? or do we just get rid of this altogether?
        ;; XXX we need to simply add 'has side-effect' to the prim table.
        ;;   [and assume external calls have side-effects]
        ;; ===================================================================
        (cps:prim n p x args t)
        -> (if #f ;; (= (vcount.get x) 0)
               (N 'dead-prim (simp venv cenv S t))
               (let ((x0 (subst/v x))
                     (args0 (map subst/v args)))
                 (cps:prim n p x0 args0 (simp venv cenv S t))))
	(cps:letcont k xs K L)
        -> (let ((xs0 (map subst/v xs))
                 (nc (ccount.get k))
                 (na (acount.get k)))
             ;; (printf "simp " (sym (cvar/name k)) " nc " (int nc) " na " (int na) "\n")
             (if (= 0 (+ nc na))
                 (N 'dead-cont (simp venv cenv S L))
                 (match (can-eta-cont? K xs0) with
                   (maybe:yes j)
                   -> (N 'eta-cont (simp venv cenv (extend-csubst S k j) L))
                   (maybe:no)
                   -> (let ((K0 (simp venv cenv S K))
                            (cenv0 (extend-cenv k (:tuple xs0 K0) cenv)))
                        (if (and (= 0 nc) (= 1 na))
                            (N 'beta-cont-1 (simp venv cenv0 S L))
                            (cps:letcont k xs0 K0 (simp venv cenv0 S L)))
                        ))))
	;; BETA-CONT
	(cps:appk k ys)
	-> (let ((k0 (subst/k k))
		 (ys0 (map subst/v ys)))
             (if (and (= 0 (ccount.get k0)) (= 1 (acount.get k0)))
                 (match (lookup-cenv k0 cenv) with
                   (maybe:yes (:tuple xs K0))
		   -> (begin
                        (trace (printf "substs: {\n"))
                        (trace (for-list2 k v xs ys0
                          (printf " : " (sym (var/name k)) (bold " = ") (sym (var/name v)) "\n")))
                        (trace (printf "}\n"))
                        (trace (dump-cps 4 K0))
                        (N 'beta-cont-2 (substitute-vars (extend-vsubst* S xs ys0) K0))
                       )
                   _ -> (cps:appk k0 ys0))
                 (cps:appk k0 ys0)
		 ))
        ;; BETA-CASE (as applied to 'if')
        (cps:if tst con alt)
        -> (match (lookup-venv tst venv) with
             (maybe:yes n)
             -> (N 'beta-case
                   (simp venv cenv S
                         (cps:appk
                          (if (zlit-zero? n) alt con)
                          (list))))
             _
             -> (cps:if tst con alt)
             )
        (cps:dead K)
        -> (cps:dead (simp venv cenv S K))
        (cps:app n k xs)
        -> (cps:app n (subst/k k) (map subst/v xs))
	)
      )
    (let loop ((n 5)
	       (exp exp))
      (set! nopt 0)
      (vcount.clear)
      (ccount.clear)
      (acount.clear)
      (census/take exp)
      ;; (printf "vcount:\n") (vcount.dump fvar)
      ;; (printf "ccount:\n") (ccount.dump fcvar)
      ;; (printf (int n) " " (cps-repr exp) "\n")
      (trace (printf (int n) "\n"))
      (trace (dump-cps 1 exp))
      (let ((exp0 (simp (alist:nil) (alist:nil)
                        (:tuple (tree/empty) (tree/empty))
                        exp)))
        (trace (printf "opt: " (int n) " " (int nopt) "\n"))
        (if (or (= nopt 0) (= n 0))
	    exp
	    (loop (- n 1) exp0)))
      )
    )
  )
