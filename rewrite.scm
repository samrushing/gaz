;; -*- Mode: Irken -*-

;; See Fig 5 in CwCC

(define (cps-repr cps)
  (repr (cps->sexp cps)))

(datatype thing
  (:val int)
  (:cont (list var) cps)
  )

(define (rewrite-cps exp)

  (let ((census (tree/empty)) ;; variable/function usage counts
        (nopt 0)) ;; count of simplifications in the current pass.

    (define (census/add key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> (set! val.count (+ val.count 1))
	(maybe:no)      -> (tree/insert! census symbol-index-cmp key {count=1})
	))

    (define (census/get key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> val.count
	(maybe:no)      -> 0
	))

    (define census/take
      (cps:letval _ x v t)       -> (census/take t)
      (cps:letcont _ k xs t0 t1) -> (begin (census/take t0) (census/take t1))
      (cps:appk _ k xs)          -> (begin (census/add k) (for-each census/add xs))
      (cps:app _ f k args)       -> (begin (census/add f) (census/add k) (for-each census/add args))
      (cps:prim _ n x args t)    -> (begin (census/add x) (for-each census/add args) (census/take t))
      (cps:if _ x k0 k1)         -> (begin (census/add x) (census/add k0) (census/add k1))
      (cps:dead _ K)             -> (census/take K)
      )

    (define (apply-subst S x)
      (match (tree/member S symbol-index-cmp x) with
	(maybe:no)    -> x
	(maybe:yes y) -> y
	))

    (define vars-eq?
      () ()               -> #t
      (h0 . t0) (h1 . t1) -> (if (eq? h0 h1) (vars-eq? t0 t1) #f)
      a b                 -> (raise (:BadArity a b))
      )

    (define (extend-subst S k v)
      (tree/insert S symbol-index-cmp k v))

    (define (extend-subst* S ks vs)
      (match ks vs with
        () ()
        -> S
        (k0 . ks) (v0 . vs)
        -> (extend-subst* (extend-subst S k0 v0) ks vs)
        _ _
        -> (raise (:BadArity ks vs))
        ))

    (define (simp env S K)

      (define (N s e)
	;; notify that a pass has a hit
        (inc! nopt)
	(printf (sym s) " " (cps-repr K) "\n")
	(printf "  : " (cps-repr e) "\n")
	e)

      (match K with
	;; DEAD-VAL
	(cps:letval t0 x V L)
	-> (if (= (census/get x) 0) ;;; XXXXX disabled by use of '<'
	       (N 'dead-val (simp env S L))
	       (let ((x0 (apply-subst S x)))
		 (cps:letval t0 x0 V (simp (alist:entry x0 (thing:val V) env) S L))))
	;; DEAD-CONT
	(cps:letcont t0 k xs K L)
        -> (let ((k0 (apply-subst S k))
                 (xs0 (map (partial (apply-subst S _)) xs)))
	     (if (= 0 (census/get k0))
	         (N 'dead-cont (simp env S L) )
	         (cps:letcont
                  t0 k0 xs0
		  (simp env S K)
		  (simp (alist:entry k0 (thing:cont xs0 K) env) S L)
		  )))
	;; BETA-CONT
	(cps:appk t0 k ys)
	-> (let ((k0 (apply-subst S k))
		 (ys0 (map (partial (apply-subst S _)) ys)))
             (if (= 1 (census/get k0))
                 (match (alist/lookup env k0) with
                   (maybe:yes (thing:cont xs K0))
		   -> (N 'beta-cont (simp env (extend-subst* S xs ys0) K0))
                   _ -> (cps:appk t0 k0 ys0)
		   )
                 (cps:appk t0 k0 ys0)
		 ))
        ;; BETA-CASE (as applied to 'if')
        (cps:if tv tst con alt)
        -> (match (alist/lookup env tst) with
             (maybe:yes (thing:val n))
             -> (begin
                  (printf ";; hey buddy, what gives?\n")
                  (N 'beta-case (simp env S (cps:appk tv (if (zero? n) alt con) (list tst))))
                  )
             _
             -> (begin
                  (printf ";; why no love?\n")
                  (cps:if tv tst con alt))
             )
        ;; ETA-CONT
        (cps:letcont t0 k xs0 (cps:appk t1 j xs1) K)
        -> (let ((j2 (apply-subst S j)))
             (if (vars-eq? xs0 xs1)
                 (N 'eta-cont (simp env (extend-subst S k j2) K))
                 (cps:letcont
                  t0 k (map (partial (apply-subst S _)) xs1)
                  (cps:appk t1 j2 xs1) (simp env S K))))
        (cps:dead t0 K)
        -> (cps:dead t0 (simp env S K))
        ;; all others
         _
         -> K
	)
      )
    (let loop ((n 5)
	       (exp exp))
      (set! nopt 0)
      (set! census (tree/empty))
      (census/take exp)
      (tree/inorder
       (lambda (k v)
         (printf (lpad 15 (symbol->string k)) " : " (lpad 5 (int v.count)) "\n"))
       census)
      (printf (int n) " " (cps-repr exp) "\n")
      (let ((exp0 (simp (alist:nil) (tree/empty) exp)))
        (if (or (= nopt 0) (= n 0))
	    exp
	    (loop (- n 1) exp0)))
      )
    )
  )
