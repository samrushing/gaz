;; -*- Mode: Irken -*-

;; XXX could this be rewritten with walk-zexp?

;;
;;   here we can also build a map from newname -> (oldname, src)
;;

;; ---- alpha conversion (renaming) ----

(define (alpha fun tenv)

  (define (R-binds env acc binds)
    (match binds with
      () -> (:tuple (reverse acc) env)
      ((:tuple vt i) . tl)
      -> (let (((vt0 env0) (extend env vt)))
           (R-binds env0 (list:cons (:tuple vt0 (RA env i)) acc) tl))
      ))

  (define (R-vars env acc vars)
    (match vars with
      () -> (:tuple (reverse acc) env)
      (var . vars)
      -> (let (((var0 env0) (extend env var)))
           (R-vars env0 (list:cons var0 acc) vars))
      ))

  (define RA
    env (azexp:t exp src typ)
    -> (azexp:t (R src env exp) src typ)
    )

  ;; XXX do we need to pass src here?  how/where will we need it?  actually I think we
  ;;     should only need it where aztname exists?
  (define R
    src env (zexp:lit n)            -> (zexp:lit n)
    src env (zexp:prim name p exps) -> (zexp:prim name p (map (partial (RA env _)) exps))
    src env (zexp:seq exps)         -> (zexp:seq (map (partial (RA env _)) exps))
    src env (zexp:let nt i body)    -> (let (((nt0 env0) (extend env nt)))
                                       (zexp:let nt0 (RA env i) (RA env0 body)))
    src env (zexp:varref name)      -> (zexp:varref (lookup env name))
    src env (zexp:if t c a)         -> (zexp:if (RA env t) (RA env c) (RA env a))
    src env (zexp:call name args)   -> (zexp:call name (map (partial (RA env _)) args))
    src env (zexp:loop k binds b)   -> (let (((k0 env0) (extend env (aztname:t k (new-tvar) src)))
                                             ((binds0 env1) (R-binds env0 (list:nil) binds)))
                                         (zexp:loop (aztname/name k0) binds0 (RA env1 b)))
    src env (zexp:appk k args)      -> (zexp:appk (lookup env k) (map (partial (RA env _)) args))
    src env (zexp:letcont k vs K L) -> (let (((vars0 env0) (R-vars env (list:nil) vs))
                                             ((k0 env1) (extend env (aztname:t k (new-tvar) src))))
                                         (zexp:letcont (aztname/name k0) vars0 (RA env0 K) (RA env1 L)))
    )

  (define gensym
    (let ((counter 0))
      (lambda (s)
        (inc! counter)
        (string->symbol (format "u_" (sym s) (int counter))))))

  (define extend
    env (aztname:t name type src)
    -> (let ((name0 (gensym name)))
         (:tuple (aztname:t name0 type src)
                 (alist:entry name name0 env)))
    )

  (define (lookup env name)
    (match (alist/lookup env name) with
      (maybe:yes name0) -> name0
      (maybe:no)        -> (raise (:UnknownVariable name))
      ))

  (define add-formals
    acc ()                                -> acc
    acc ((aztname:t vname type src) . tl) -> (add-formals (alist:entry vname vname acc) tl)
    )

  (define add-tenv
    acc (alist:nil)                -> acc
    acc (alist:entry name type tl) -> (add-tenv (alist:entry name name acc) tl)
    )

  ;; XXX this is where we lose all info about renamings!  in a real compiler we should
  ;;   keep a global map of such renamings, so we can trace any variable to its original
  ;;   location in the source.
  (match fun with
    (ztop:fun name formals body)
    -> (let ((env0 (add-tenv (alist:nil) tenv))
             (env1 (add-formals env0 formals)))
         (ztop:fun name formals (RA env1 body)))
    otherwise
    -> otherwise
    )
  )

