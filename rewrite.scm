;; -*- Mode: Irken -*-

;; See Fig 5 in CwCC

(define (cps-repr cps)
  (repr (cps->sexp cps)))

;; this is over-complicated by the var/cvar distinction.

(define fvar  (var:t name _) -> (format (sym name)))
(define fcvar (cvar:t name)  -> (format (sym name)))

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
    {add=add get=get dump=dump}
    ))

(define cmp-var
  (var:t a _) (var:t b _) -> (symbol-index-cmp a b)
  )
(define cmp-cvar
  (cvar:t a) (cvar:t b) -> (symbol-index-cmp a b)
  )

(define (rewrite-cps exp)

  (let ((vcount (make-census cmp-var))  ;; variable/function usage counts
        (ccount (make-census cmp-cvar)) ;; continuation usage counts
        (nopt 0)) ;; count of simplifications in the current pass.

    (define census/take
      (cps:letval x v t)       -> (census/take t)
      (cps:letcont k xs t0 t1) -> (begin (census/take t0) (census/take t1))
      (cps:appk k xs)          -> (begin (ccount.add k) (for-each vcount.add xs))
      (cps:app f k args)       -> (begin (ccount.add k) (for-each vcount.add args))
      (cps:prim n p x args t)  -> (begin (for-each vcount.add args) (census/take t))
      (cps:if x k0 k1)         -> (begin (vcount.add x) (ccount.add k0) (ccount.add  k1))
      (cps:dead K)             -> (census/take K)
      )

    (define (apply-subst S cmp x)
      (match (tree/member S cmp x) with
	(maybe:no)    -> x
	(maybe:yes y) -> y
	))

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

    (define (simp venv cenv S K)

      ;; XXX get rid of the `partial`s below by moving apply/extends in here?

      (define (N s e)
	;; notify that a pass has a hit
        (inc! nopt)
	;; (printf (sym s) " " (cps-repr K) "\n")
	;; (printf "  : " (cps-repr e) "\n")
	e)

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
        ;; ===================================================================

        (cps:prim n p x args t)
        -> (if #f ;; (= (vcount.get x) 0)
               (N 'dead-prim (simp venv cenv S t))
               (let ((x0 (apply-vsubst S x))
                     (args0 (map (partial (apply-vsubst S _)) args)))
                 (cps:prim n p x0 args0 (simp venv cenv S t))))
        ;; ETA-CONT
        (cps:letcont k xs0 (cps:appk j xs1) K)
        -> (let ((j2 (apply-csubst S j)))
             (if (vars-eq? xs0 xs1)
                 (N 'eta-cont (simp venv cenv (extend-csubst S k j2) K))
                 (let ((xs0* (map (partial (apply-vsubst S _)) xs0))
                       (xs1* (map (partial (apply-vsubst S _)) xs1)))
                   (cps:letcont
                    k xs0*
                    (cps:appk j2 xs1*)
                    (simp venv cenv S K) ;; XXX extend cenv?
                    ;; this might be what's needed *if so*
                    ;;(simp venv (extend-cenv k (:tuple xs2 (cps:appk j2 xs1)) cenv) S K)
                    ))))
	;; DEAD-CONT
	(cps:letcont k xs K L)
        -> (let ((k0 (apply-csubst S k))
                 (xs0 (map (partial (apply-vsubst S _)) xs))) ;; XXX move below
	     (if (= 0 (ccount.get k0))
	         (N 'dead-cont (simp venv cenv S L) )
	         (cps:letcont
                  k0 xs0
		  (simp venv cenv S K)
		  (simp venv (extend-cenv k0 (:tuple xs0 K) cenv) S L)
		  )))
	;; BETA-CONT
	(cps:appk k ys)
	-> (let ((k0 (apply-csubst S k))
		 (ys0 (map (partial (apply-vsubst S _)) ys)))
             (if (= 1 (ccount.get k0))
                 (match (lookup-cenv k0 cenv) with
                   (maybe:yes (:tuple xs K0))
		   -> (N 'beta-cont (simp venv cenv (extend-vsubst* S xs ys0) K0))
                   _ -> (cps:appk k0 ys0)
		   )
                 (cps:appk k0 ys0)
		 ))
        ;; BETA-CASE (as applied to 'if')
        (cps:if tst con alt)
        -> (match (lookup-venv tst venv) with
             (maybe:yes n)
             -> (N 'beta-case (simp venv cenv S (cps:appk (if (zero? n) alt con) (list))))
             _
             -> (cps:if tst con alt)
             )
        (cps:dead K)
        -> (cps:dead (simp venv cenv S K))
        ;; all others
        ;; XXX anything else still probably needs to be walked for simp
        ;;     of sub-expressions???
        ;; XXX for example, no handler for cps:app here.
         _
         -> (begin
              (printf (bold "yes, this happens\n"))
              K
              )
	)
      )
    (let loop ((n 5)
	       (exp exp))
      (set! nopt 0)
      (set! vcount (make-census cmp-var))
      (set! ccount (make-census cmp-cvar))
      (census/take exp)
      (printf "vcount:\n") (vcount.dump fvar)
      (printf "ccount:\n") (ccount.dump fcvar)
      ;;(printf (int n) " " (cps-repr exp) "\n")
      ;; (printf (int n) "\n")
      ;; (dump-cps 1 exp)
      (let ((exp0 (simp (alist:nil) (alist:nil)
                        (:tuple (tree/empty) (tree/empty))
                        exp)))
        (if (or (= nopt 0) (= n 0))
	    exp
	    (loop (- n 1) exp0)))
      )
    )
  )
