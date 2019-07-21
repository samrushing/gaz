;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/partial.scm")
(require "./cps.scm")
(require "./rewrite.scm")

;; ---- datatypes ----

(datatype clexp
  (:lit int)                            ;; value
  (:prim symbol (list clexp))           ;; name args
  (:seq (list clexp))                   ;; exp ...
  (:let symbol clexp clexp)             ;; name init body
  (:ref symbol)                         ;; name
  (:set symbol clexp)                   ;; name value
  (:if clexp clexp clexp)               ;; test con ant
  (:call symbol (list clexp))           ;; name args
  )

(datatype clfun
  (:t name (list symbol) clexp)
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
    )
  (E exp)
  )

;; ---- parse ----

(define (parse-clexp exp)

  (define p-bindings
    body ()
    -> body
    body ((sexp:list ((sexp:symbol name) init)) . rest)
    -> (clexp:let name (p-exp init) (p-bindings body rest))
    body x
    -> (raise (:SyntaxError (sexp:list x)))
    )

  (define p-exp-list
    ((sexp:symbol 'begin) . rest)                 -> (clexp:seq (map p-exp rest))
    ((sexp:symbol 'set!) (sexp:symbol name) val)  -> (clexp:set name (p-exp val))
    ((sexp:symbol 'if) test con ant)              -> (clexp:if (p-exp test) (p-exp con) (p-exp ant))
    ((sexp:symbol 'let) (sexp:list binds) . body) -> (p-bindings (p-body '() body) binds)
    ((sexp:symbol fun) . args)                    -> (clexp:call fun (map p-exp args))
    x                                             -> (raise (:SyntaxError (sexp:list x)))
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

  ;; make this instead the entry point, and segregate the result into
  ;; functions and a single body.  [or maybe replace clfun with clfix]
  ;; [in irken this would be 'parse-body', which might include definitions,
  ;;  which are arranged into a fix after toposort].
  (define p-define
    ((sexp:symbol 'define)
     (sexp:list ((sexp:symbol name) . formals))
     . body)
    -> (clfun:t name (p-formals '() formals) (p-body '() body))
    exp
    -> (raise (:SyntaxError (sexp:list exp)))
    )

  (define p-exp
    (sexp:int v)    -> (clexp:lit v)
    (sexp:symbol s) -> (clexp:ref s)
    (sexp:list vs)  -> (p-exp-list vs)
    x               -> (raise (:SyntaxError x))
    )

  (p-exp exp)
  )

;; ---- alpha conversion (renaming) ----

;; XXX I wonder if this is even needed? for inlining? will we be doing inlining?

(define (alpha exp)

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

  ;; XXX this is where we lose all info about renamings!  in a real compiler we should
  ;;   keep a global map of such renamings, so we can trace any variable to its original
  ;;   location in the source.
  (R (alist:nil) exp)
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
        (forms (read-file ipath)))
    (for-list form forms
      (let ((exp0 (parse-clexp form))
            (exp1 (alpha exp0))
            (cps0 (clexp->cps exp1))
            (cps1 (rewrite-cps cps0)))
        (pp0 form 80 0 "; ")
        (pp0 (clexp->sexp exp0) 80 0 "; ")
        (pp0 (clexp->sexp exp1) 80 0 "; ")
        (pp0 (cps->sexp cps0) 80 0 "; ")
        (pp0 (cps->sexp cps1) 80 0 "; ")
        (printf "\n")
        (cps->llvm cps0)
        (printf "\n")
        (cps->llvm cps1)
      ))))

(main)
