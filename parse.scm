;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/partial.scm")
(require "./cps.scm")
(require "./rewrite.scm")
;(require "./cps2llvm.scm")

;; ---- datatypes ----

(datatype clexp
  (:lit int)                       ;; value
  (:prim symbol (list clexp))      ;; name args
  (:seq (list clexp))              ;; exp ...
  (:let symbol clexp clexp)        ;; name init body
  (:ref symbol)                    ;; name
  (:set symbol clexp)              ;; name value
  (:if clexp clexp clexp)          ;; test con ant
  (:call symbol (list clexp))      ;; name args
  (:loop symbol                    ;; name
         (list (:tuple var clexp)) ;; bindings
         clexp)                    ;; body
  (:appk symbol (list clexp))      ;; kname arg
  )

(datatype clfun
  (:t symbol (list symbol) clexp)
  )

;; ---- unparse ----

(define (clexp->sexp exp)
  (define E
    (clexp:lit n)              -> (sexp (sym 'lit) (int n))
    (clexp:prim name args)     -> (sexp (sym name) (list (map E args)))
    (clexp:seq exps)           -> (sexp1 'seq (map E exps))
    (clexp:let name init body) -> (sexp (sym 'let) (sym name) (E init) (E body))
    (clexp:ref name)           -> (sexp (sym 'ref) (sym name))
    (clexp:set name val)       -> (sexp (sym 'set) (sym name) (E val))
    (clexp:if t c a)           -> (sexp (sym 'if) (E t) (E c) (E a))
    (clexp:call n args)        -> (sexp (sym 'call) (sym n) (list (map E args)))
    (clexp:loop n binds b)     -> (sexp (sym 'loop) (sym n)
                                        (list (map (lambda (:tuple v i)
                                                     (sexp (sym v) (E i)))
                                                   binds))
                                        (E b))
    (clexp:appk n args)        -> (sexp (sym 'appk) (sym n) (list (map E args)))
    )
  (E exp)
  )

;; ---- parse ----

(define (parse-clexp exp)

  (define p-let-bindings
    body ()
    -> body
    body ((sexp:list ((sexp:symbol name) init)) . rest)
    -> (clexp:let name (p-exp init) (p-let-bindings body rest))
    body x
    -> (raise (:SyntaxError (sexp:list x)))
    )

  (define p-binding
    (sexp:list ((sexp:symbol var) init)) -> (:tuple var (p-exp init))
    x -> (raise (:SyntaxError x))
    )

  (define p-exp-list
    ((sexp:symbol 'begin) . rest)                  -> (clexp:seq (map p-exp rest))
    ((sexp:symbol 'set!) (sexp:symbol name) val)   -> (clexp:set name (p-exp val))
    ((sexp:symbol 'if) test con ant)               -> (clexp:if (p-exp test)
                                                               (p-exp con)
                                                               (p-exp ant))
    ((sexp:symbol 'let) (sexp:list binds)  . body) -> (p-let-bindings (p-body '() body) binds)
    ((sexp:symbol 'appk) (sexp:symbol k) . args)   -> (clexp:appk kname (map p-exp args))
    ((sexp:symbol 'loop) (sexp:list binds) . body) -> (clexp:loop kname
                                                                  (map p-binding binds)
                                                                  (p-body '() body))
    ((sexp:symbol fun) . args)                     -> (clexp:call fun (map p-exp args))
    x                                              -> (raise (:SyntaxError (sexp:list x)))
    )

  (define p-formals
    ;; XXX add types
    acc ()                            -> (reverse acc)
    acc ((sexp:symbol formal) . rest) -> (p-formals (list:cons formal acc) rest)
    acc x                             -> (raise (:SyntaxError (sexp:list x)))
    )

  (define p-body
    ()  ()           -> (raise (:EmptyBody))
    (one) ()         -> one
    acc ()           -> (clexp:seq (reverse acc))
    acc (exp . rest) -> (p-body (list:cons (p-exp exp) acc) rest)
    )

  (define (parse exp)
    (match exp with
      ;; function definition
      (sexp:list ((sexp:symbol 'define) (sexp:list ((sexp:symbol name) . formals)) . body))
      -> (:fun (clfun:t name (p-formals '() formals) (p-body '() body)))
      (sexp:list ((sexp:symbol 'define) (sexp:symbol name) exp))
      ;; global variable definition
      -> (raise (:NotImplemented exp))
      exp
      -> (:exp (p-exp exp))
      ))

  (define p-exp
    (sexp:int v)    -> (clexp:lit v)
    (sexp:symbol s) -> (clexp:ref s)
    (sexp:list vs)  -> (p-exp-list vs)
    x               -> (raise (:SyntaxError x))
    )

  (parse exp)
  )

(define (parse-toplevel forms)
  (let ((exps (list:nil))
        (funs (list:nil)))
    (for-list form forms
      (match (parse-clexp form) with
        (:fun f) -> (push! funs f)
        (:exp e) -> (push! exps e)
        ))
    (:tuple (reverse funs) (reverse exps))
    ))

;; ---- alpha conversion (renaming) ----

(define (alpha exp args)

  (define (R-binds env acc binds)
    (match binds with
      () -> (:tuple (reverse acc) env)
      ((:tuple v i) . tl)
      -> (R-binds (extend env v) (list:cons (R env i) acc) tl)
      ))

  (define R
    env (clexp:lit n)          -> (clexp:lit n)
    env (clexp:prim name exps) -> (clexp:prim name (map (partial (R env _)) exps))
    env (clexp:seq exps)       -> (clexp:seq (map (partial (R env _)) exps))
    env (clexp:let n i body)   -> (let (((n0 env0) (extend env n)))
                                    (clexp:let n0 (R env i) (R env0 body)))
    env (clexp:ref name)       -> (clexp:ref (lookup env name))
    env (clexp:set name val)   -> (clexp:set (lookup env name) (R env val))
    env (clexp:if t c a)       -> (clexp:if (R env t) (R env c) (R env a))
    env (clexp:call name args) -> (clexp:call name (map (partial (R env _)) args))
    env (clexp:loop k binds b) -> (let (((k0 env0) (extend env k))
                                        ((binds0 env1) (R-binds env0 (list:nil) env0)))
                                    (clexp:loop k0 binds0 (R env1 b)))
    env (clexp:appk k args)    -> (clexp:appk (lookup env k) (map (partial (R env _)) args))
    )

  (define gensym
    (let ((counter 0))
      (lambda (s)
        (inc! counter)
        (string->symbol (format (sym s) (int counter))))))

  (define (extend env name)
    (let ((name0 (gensym name)))
      (:tuple name0 (alist:entry name name0 env))))

  (define (lookup env name)
    (match (alist/lookup env name) with
      (maybe:yes name0) -> name0
      (maybe:no)        -> (raise (:UnknownVariable name))
      ))

  (define initial-env
    acc ()        -> acc
    acc (hd . tl) -> (initial-env (alist:entry hd hd acc) tl)
    )

  ;; XXX this is where we lose all info about renamings!  in a real compiler we should
  ;;   keep a global map of such renamings, so we can trace any variable to its original
  ;;   location in the source.
  (R (initial-env (alist:nil) args) exp)
  )

;; ---- modified pprint ----

(define (pp0 exp width depth prefix)
  (define (recur d exp)
    (let ((size (pp-size exp)))
      (if (< size width)
	  (printf (repr exp))
	  (match exp with
	    (sexp:list ())
	    -> (printf "()")
	    (sexp:list (hd . tl))
	    -> (begin (printf "(")
		      (recur d hd)
		      (for-each
		       (lambda (x)
			 (newline)
                         (printf prefix)
			 (indent (+ d 1))
			 (recur (+ d 1) x)) tl)
		      (printf ")"))
	    ;; XXX complete for vector & record.
	    _ -> (printf (repr exp))))))
  (printf prefix)
  (recur depth exp)
  (print-string "\n")
  )

;; ---- file input ----

(define (read-file path)
  (let ((file (file/open-read path))
	(result (reader path (lambda () (file/read-char file)))))
    result))

(define (main)
  (let ((ipath sys.argv[1])
        (forms (read-file ipath))
        ((funs exps) (parse-toplevel forms)))
    (when (> (length exps) 0)
      (raise (:NoToplevelExps)))
    (for-list fun funs
      (match fun with
        (clfun:t name args exp0)
        -> (let ((exp1 (alpha exp0 args))
                 (cps0 (clexp->cps exp1))
                 (cps1 (rewrite-cps cps0)))
             (pp0 (clexp->sexp exp0) 80 0 "; ")
             ;; (pp0 (clexp->sexp exp1) 80 0 "; ")
             (pp0 (cps->sexp cps0) 80 0 "; ")
             (pp0 (cps->sexp cps1) 80 0 "; ")
             ;; (printf "\n")
             ;; (cps->llvm cps0)
             (printf "\n")
             ;;(cpsfun->llvm name args cps0)
             )))))

(main)
