;; -*- Mode: Irken -*-

(define (cps-repr cps)
  (repr (cps->sexp cps)))

(datatype thing
  (:val int)
  (:cont (list var) cps)
  )

(define (rewrite-cps exp)

  (let ((census (tree/empty)))

    (define (increment-census key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> (set! val.count (+ val.count 1))
	(maybe:no)      -> (tree/insert! census symbol-index-cmp key {count=1})
	))

    (define (census/get key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> val.count
	(maybe:no)      -> 0
	))

    (define take-census
      (cps:let n x t)          -> (begin (increment-census x) (take-census t))
      (cps:ref n x t)          -> (begin (increment-census x) (take-census t))
      (cps:set n x t)          -> (begin (increment-census x) (take-census t))
      (cps:letval x v t)       -> (take-census t)
      (cps:letcont k xs t0 t1) -> (begin (take-census t0) (take-census t1))
      (cps:appk k xs)          -> (begin (increment-census k)
                                         (for-each increment-census xs))
      (cps:app f k args)       -> (begin (increment-census f)
                                         (increment-census k)
                                         (for-each increment-census args))
      (cps:prim n x args t)    -> (begin (increment-census x)
                                         (for-each increment-census args)
                                         (take-census t))
      (cps:if x k0 k1)         -> (begin (increment-census x)
                                         (increment-census k0)
                                         (increment-census k1))
      (cps:dead K)             -> (take-census K)
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
	(printf (sym s) " " (cps-repr K) "\n")
	(printf "  : " (cps-repr e) "\n")
	e)

      (match K with
        (cps:let name x K)
        -> (cps:let name (apply-subst S x) (simp env S K))
        (cps:ref name x K)
        -> (cps:ref name (apply-subst S x) (simp env S K))
        (cps:set name x K)
        -> (cps:set name (apply-subst S x) (simp env S K))
        ;; ETA-CONT
        (cps:letcont k xs0 (cps:appk j xs1) K)
        -> (let ((j2 (apply-subst S j)))
             (if (vars-eq? xs0 xs1)
                 (N 'eta-cont (simp env (extend-subst S k j2) K))
                 (cps:letcont
                  k (map (lambda (y) (apply-subst S y)) xs1)
                  (cps:appk j2 xs1) (simp env S K))))
	;; DEAD-VAL
	(cps:letval x V L)
	-> (if (= (census/get x) 0) ;;; XXXXX disabled by use of '<'
	       (N 'dead-val (simp env S L))
	       (let ((x0 (apply-subst S x)))
		 (cps:letval x0 V (simp (alist:entry x0 (thing:val V) env) S L))))
	;; DEAD-CONT
	;; XXX I think the paper gets this confusingly wrong...
	(cps:letcont k xs K L)
        -> (let ((k0 (apply-subst S k))
                 (xs0 (map (lambda (y) (apply-subst S y)) xs)))
	     (if (= 0 (census/get k0))
	         (N 'dead-cont (simp env S L) )
	         (cps:letcont
                  k0 xs0
		  (simp env S K)
		  (simp (alist:entry k0 (thing:cont xs0 K) env) S L)
		  )))
	;; BETA-CONT
	(cps:appk k ys)
	-> (let ((k0 (apply-subst S k))
		 (ys0 (map (lambda (x) (apply-subst S x)) ys)))
             (if (= 1 (census/get k0))
                 (match (alist/lookup env k0) with
                   (maybe:yes (thing:cont xs K0))
		   -> (N 'beta-cont (simp env (extend-subst* S xs ys0) K0))
                   _ -> (cps:appk k0 ys0)
		   )
                 (cps:appk k0 ys0)
		 ))
        (cps:dead K)
        -> (cps:dead (simp env S K))
        ;; all others
         _
         -> K
	)
      )
    (let loop ((n 5)
	       (exp exp))
      (set! census (tree/empty))
      (take-census exp)
      (tree/inorder
       (lambda (k v)
         (printf (lpad 15 (symbol->string k)) " : " (lpad 5 (int v.count)) "\n"))
       census)
      (printf (int n) " " (cps-repr exp) "\n")
      (if (= n 0)
	  exp
	  (loop (- n 1) (simp (alist:nil) (tree/empty) exp))))
    )
  )
