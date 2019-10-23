;; -*- Mode: Irken -*-

;; See Fig 5 in CwCC

(define (cps-repr cps)
  (repr (cps->sexp cps)))

;; XXX the env alist has two different types of entries `[k,v]`
;;  and this hack used to handle the difference in `v`, but now
;;  needs to handle the difference in `k`.  All this is caused by
;;  our decision to have `var` and `cvar` be two different types.
;;  Q: IS IT WORTH IT?
;;  think about how much more complicated this might get with more
;;    rewrites added.
;;  maybe just add helper funs for extending the environment rather
;;    than using alist:entry directly?

(datatype thing
  (:val int)
  (:cont (list var) cps)
  )

(define (rewrite-cps exp)

  (let ((census (tree/empty)) ;; variable/function usage counts
        (nopt 0)) ;; count of simplifications in the current pass.

    (define census/cadd (cvar:t name _) -> (census/add name))
    (define census/vadd (var:t name _)  -> (census/add name))

    (define (census/add key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> (set! val.count (+ val.count 1))
	(maybe:no)      -> (tree/insert! census symbol-index-cmp key {count=1})
	))

    (define census/vget (var:t name _)  -> (census/get name))
    (define census/cget (cvar:t name _) -> (census/get name))

    (define (census/get key)
      (match (tree/member census symbol-index-cmp key) with
	(maybe:yes val) -> val.count
	(maybe:no)      -> 0
	))

    (define census/take
      (cps:letval x v t)       -> (census/take t)
      (cps:letcont k xs t0 t1) -> (begin (census/take t0) (census/take t1))
      (cps:appk k xs)          -> (begin (census/cadd k) (for-each census/vadd xs))
      (cps:app f k args)       -> (begin (census/add f) (census/cadd k) (for-each census/vadd args))
      (cps:prim n x args t)    -> (begin (for-each census/vadd args) (census/take t))
      (cps:if x k0 k1)         -> (begin (census/vadd x) (census/cadd k0) (census/cadd k1))
      (cps:dead K)             -> (census/take K)
      )


    (define apply-vsubst
      S (var:t x ty) -> (var:t (apply-subst S x) ty)
      )
    (define apply-csubst
      S (cvar:t k ty) -> (cvar:t (apply-subst S k) ty)
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
	(cps:letval x V L)
	-> (if (= (census/vget x) 0) ;;; XXXXX disabled by use of '<'
	       (N 'dead-val (simp env S L))
	       (let ((x0 (apply-vsubst S x)))
		 (cps:letval x0 V (simp (alist:entry x0 (thing:val V) env) S L))))
        ;; DEAD-PRIM cps:prim also binds a value
        (cps:prim n x args t)
        -> (if (= (census/vget x) 0)
               (N 'dead-prim (simp env S t))
               (let ((x0 (apply-vsubst S x)))
                 (cps:prim n x0 args (simp env S t))))
        ;; ETA-CONT
        (cps:letcont k xs0 (cps:appk j xs1) K)
        -> (let ((j2 (apply-csubst S j)))
             (if (vars-eq? xs0 xs1)
                 (N 'eta-cont (simp env (extend-subst S k j2) K))
                 (cps:letcont
                  k (map (partial (apply-vsubst S _)) xs1)
                  (cps:appk j2 xs1) (simp env S K))))
	;; DEAD-CONT
	(cps:letcont k xs K L)
        -> (let ((k0 (apply-csubst S k))
                 (xs0 (map (partial (apply-vsubst S _)) xs)))
	     (if (= 0 (census/cget k0))
	         (N 'dead-cont (simp env S L) )
	         (cps:letcont
                  k0 xs0
		  (simp env S K)
		  (simp (alist:entry k0 (thing:cont xs0 K) env) S L)
		  )))
	;; BETA-CONT
	(cps:appk k ys)
	-> (let ((k0 (apply-csubst S k))
		 (ys0 (map (partial (apply-vsubst S _)) ys)))
             (if (= 1 (census/cget k0))
                 (match (alist/lookup env k0) with
                   (maybe:yes (thing:cont xs K0))
		   -> (N 'beta-cont (simp env (extend-subst* S xs ys0) K0))
                   _ -> (cps:appk k0 ys0)
		   )
                 (cps:appk k0 ys0)
		 ))
        ;; BETA-CASE (as applied to 'if')
        (cps:if tst con alt)
        -> (match (alist/lookup env tst) with
             (maybe:yes (thing:val n))
             -> (N 'beta-case (simp env S (cps:appk (if (zero? n) alt con) (list tst))))
             _
             -> (cps:if tst con alt)
             )
        (cps:dead K)
        -> (cps:dead (simp env S K))
        ;; all others
        ;; XXX anything else still probably needs to be walked for simp
        ;;     of sub-expressions???
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
