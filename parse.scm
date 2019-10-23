;; -*- Mode: Irken -*-

;; ---- datatypes ----

(datatype clexp
  (:lit int)                       ;; value
  (:prim symbol (list clexp))      ;; name args
  (:seq (list clexp))              ;; exp ...
  (:let symbol type clexp clexp)   ;; name type init body
  (:ref symbol)                    ;; name
  (:set symbol clexp)              ;; name value
  (:if clexp clexp clexp)          ;; test con alt
  (:call symbol (list clexp))      ;; name args
  (:loop symbol                    ;; loopname,
         (list (:tuple (:tuple symbol type) clexp)) ;; inits,
         clexp)                       ;; body
  (:appk symbol (list clexp))      ;; kname arg
  )

(datatype clfun
  (:t symbol (list (:tuple symbol type)) clexp)
  )

;; ---- unparse ----

(define (clexp->sexp exp)

  (define T type->sexp)

  (define B
    (:tuple (:tuple v t) i) -> (sexp (sym v) (T t) (E i))
    )

  (define E
    (clexp:lit n)                -> (sexp (sym 'lit) (int n))
    (clexp:prim name args)       -> (sexp (sym name) (list (map E args)))
    (clexp:seq exps)             -> (sexp1 'seq (map E exps))
    (clexp:let name t init body) -> (sexp (sym 'let) (sym name) (T t) (E init) (E body))
    (clexp:ref name)             -> (sexp (sym 'ref) (sym name))
    (clexp:set name val)         -> (sexp (sym 'set) (sym name) (E val))
    (clexp:if t c a)             -> (sexp (sym 'if) (E t) (E c) (E a))
    (clexp:call n args)          -> (sexp (sym 'call) (sym n) (list (map E args)))
    (clexp:loop n binds b)       -> (sexp (sym 'let) (sym n) (list (map B binds)) (E b))
    (clexp:appk n args)          -> (sexp (sym 'appk) (sym n) (list (map E args)))
    )
  (E exp)
  )

(define typed-var->sexp
  (:tuple vname type) -> (sexp (sym vname) (type->sexp type))
  )

(define clfun->sexp
  (clfun:t name binds body)
  -> (sexp (sym 'define) (sexp1 name (map typed-var->sexp binds))
           (clexp->sexp body)))

;; ---- parse ----

(define (parse-clexp exp)

  (define p-typed-var
    ;; the irken reader will emit (sexp:cons 'x 'y) for `x:y`
    ;;   for constructors.  I'm not super happy with that and
    ;;   would prefer a (sexp:colon) as a generic infix expression.
    (asexp:cons vname type)
    -> (:tuple vname (parse-type (asexp:symbol type)))
    (asexp:list ((asexp:symbol '%typed) (asexp:symbol vname) type))
    -> (:tuple vname (parse-type type))
    x -> (begin
           (printf "bad: " (sexp x) "\n")
           (raise (:SyntaxError 0 x)))
    )

  (define p-let-bindings
    body ()
    -> body
    body ((asexp:list (var init)) . rest)
    -> (let (((vname type) (p-typed-var var)))
         (clexp:let vname type (p-exp init) (p-let-bindings body rest)))
    body x
    -> (raise (:SyntaxError 1 (asexp:list x)))
    )

  (define p-binding
    (asexp:list (var init)) -> (:tuple (p-typed-var var) (p-exp init))
    x -> (raise (:SyntaxError 2 x))
    )

  (define p-exp-list
    ((asexp:symbol 'begin) . rest)                  -> (clexp:seq (map p-exp rest))
    ((asexp:symbol 'set!) (asexp:symbol name) val)   -> (clexp:set name (p-exp val))
    ((asexp:symbol 'if) test con alt)               -> (clexp:if (p-exp test) (p-exp con) (p-exp alt))
    ((asexp:symbol 'let) (asexp:list binds)  . body) -> (p-let-bindings (p-body '() body) (strip-ann1 binds))
    ((asexp:symbol 'appk) (asexp:symbol k) . args)   -> (clexp:appk k (map p-exp args))
    ((asexp:symbol 'let)
     (asexp:symbol loopname)
     (asexp:list binds) . body)                     -> (clexp:loop loopname
                                                                  (map p-binding (strip-ann1 binds))
                                                                  (p-body '() body))
    ((asexp:symbol fun) . args)                     -> (clexp:call fun (map p-exp args))
    x                                              -> (raise (:SyntaxError 3 (asexp:list x)))
    )

  (define p-formals
    acc ()              -> (reverse acc)
    acc (formal . rest) -> (p-formals (list:cons (p-typed-var formal) acc) rest)
    )

  (define p-body
    ()  ()           -> (raise (:EmptyBody))
    (one) ()         -> one
    acc ()           -> (clexp:seq (reverse acc))
    acc (exp . rest) -> (p-body (list:cons (p-exp exp) acc) rest)
    )

  (define p-formals
    ((asexp:symbol name) . formals) -> (:tuple name (map p-typed-var formals))
    x -> (raise (:SyntaxError 4 (asexp:list x)))
    )

  (define (parse exp)
    (match exp with
      ;; function definition
      (asexp:list ((asexp:symbol 'define) (asexp:list ((asexp:symbol name) . formals)) . body))
      -> (:fun (clfun:t name (p-formals '() formals) (p-body '() body)))
      (sexp:list ((sexp:symbol 'define) (sexp:symbol name) exp))
      ;; global variable definition
      -> (raise (:NotImplemented exp))

  (define p-exp
    (sexp:int v)    -> (clexp:lit v)
    (sexp:symbol s) -> (clexp:ref s)
    (sexp:list vs)  -> (p-exp-list vs)
    x               -> (raise (:SyntaxError 6 x))
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
      ((:tuple (:tuple v t) i) . tl)
      -> (let (((v0 env0) (extend env v)))
           (R-binds env0 (list:cons (:tuple (:tuple v0 t) (R env i)) acc) tl))
      ))

  (define R
    env (clexp:lit n)          -> (clexp:lit n)
    env (clexp:prim name exps) -> (clexp:prim name (map (partial (R env _)) exps))
    env (clexp:seq exps)       -> (clexp:seq (map (partial (R env _)) exps))
    env (clexp:let n t i body) -> (let (((n0 env0) (extend env n)))
                                    (clexp:let n0 t (R env i) (R env0 body)))
    env (clexp:ref name)       -> (clexp:ref (lookup env name))
    env (clexp:set name val)   -> (clexp:set (lookup env name) (R env val))
    env (clexp:if t c a)       -> (clexp:if (R env t) (R env c) (R env a))
    env (clexp:call name args) -> (clexp:call name (map (partial (R env _)) args))
    env (clexp:loop k binds b) -> (let (((k0 env0) (extend env k))
                                        ((binds0 env1) (R-binds env0 (list:nil) binds)))
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
    acc ((:tuple vname type) . tl) -> (initial-env (alist:entry vname vname acc) tl)
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

