;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/cmap.scm")
(require "lib/partial.scm")
(require "./read.scm")
(require "./parsec.scm")
(require "./types.scm")
(require "./lazy.scm")
(require "./zexp.scm")
(require "./parse.scm")
(require "./alpha.scm")
(require "./cps.scm")
(require "./rewrite.scm")
(require "./solve.scm")
(require "./cps2llvm.scm")

;; ----- testing -----

(define (parse-file path)
  (let ((p (zp-top))
        (ifile (file/open-read path))
        (read-char (lambda () (file/read-char ifile)))
        (exps (read2 path read-char #t))
        (result '()))
    ;;(pp0 (first exp0) 80 0 "")
    (for-list exp exps
      (match (p.fun (list exp)) with
        (result:no src label err)
        -> (begin
             (printf (bold "parse fail") " while reading " (repr label) "\n")
             (printf "err = " err "\n")
             (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
             (raise (:ParseFail)))
        (result:fail src label err)
        -> (begin
             (printf (bold "parse fail") " while reading " (repr label) "\n")
             (printf "err = " err "\n")
             (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
             (raise (:ParseFail)))
        (result:ok src top rest) ;; note: ignoring `rest`
        -> (begin
             (printf "result:\n")
             (dump-ztop top) (printf "\n")
             (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
             (push! result (:tuple src top)))
             ))
    (file/close ifile)
    result))

;; TODO
;;
;;  X * parse to zfun
;;  X * cps2llvm needs to be taught about types.
;;  * do 'something' with src information
;;     * eventually fix/test parse errors
;;  X * add type checking
;;  X * propagate type info all the way down to llvm
;;  X * calling external functions.
;;      I think this is basically `prim`, since it is binding
;;        a new value and acts like a single insn.
;;  * MBE
;;  * implement `ref` and `set!`.
;;  * rename 'halt' to 'return'? [this kinda depends on if/when we'll add (internal) functions]
;;  * collect types from defined functions, put them in the type env.
;;
;;  [eventually]
;;  * revisit the awfulness that is the parser AGAIN.
;;    I think it might be possible to do something like parsec, but simplified
;;    and more s-expression friendly?

;; XXX options

(define (main)

  (define formals->tenv
    env ()                        -> env
    env ((aztname:t x tx _) . tl) -> (formals->tenv (alist:entry x tx env) tl)
    )

  (let ((path sys.argv[1])
        (tops (parse-file sys.argv[1]))
        (tenv (alist:nil))
        (funs '())
        (compiled '())
        )
    (for-list top tops
      (match top with
        (:tuple src top)
        -> (match top with
             (ztop:fun _ _ _)      -> (push! funs top)
             (ztop:decl name type) -> (alist/push tenv name type)
             )))
    (for-list fun (reverse funs)
      (match (alpha fun) with
        (ztop:fun name formals body)
        -> (let ((tenv0 (formals->tenv tenv formals))
                 (cps0 (zexp->cps tenv0 body))
                 ;;(cps1 (rewrite-cps cps0))
                 (cps1 cps0)
                 (rtype (new-tvar)))
             (printf "\ncps0:\n")
             (dump-cps 0 cps0)
             (printf "\ncps1:\n")
             (dump-cps 0 cps1)
             (solve tenv (alist:entry 'halt (list rtype) (alist:nil)) cps1)
             (let ((cps2 (cps-subst cps1)))
               (printf "\ntyped:\n")
               (dump-cps 0 cps2)
               (push! compiled (:tuple name rtype formals cps2))
             ))
        _
        -> #u
        ))
    (compiled->llvm path tenv compiled)
    ))

(main)

