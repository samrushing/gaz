;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/cmap.scm")
(require "lib/partial.scm")
(require "lib/getopt.scm")
(require "./read.scm")
(require "./macros.scm")
(require "./parse.scm")
(require "./zexp.scm")
(require "./types.scm")
(require "./alpha.scm")
(require "./cps.scm")
(require "./rewrite.scm")
(require "./solve.scm")
(require "./llvm.scm")
(require "./eval.scm")

(define program-options
  (makeopt
   (flag 'eval)
   (flag 'quiet)
   (flag 'v)
   (flag 'nr)
   (pos+ 'paths (string))
   ))

(define (get-options)
  (try
   (process-options program-options (rest (vector->list sys.argv)))
   except
   (:Getopt/MissingArg _ _) -> (usage)
   (:Getopt/UnknownArg _ _) -> (usage)
   ))

(define (usage)
  (printf "Gaz compiler.\n\n")
  (printf "Usage: " sys.argv[0] " <src>\n"
          "  [-eval] invoke the interpreter (requires a 'main' function).\n"
          "  [-v] verbose output.\n"
          "  [-nr] no rewrite phase.\n"
          "example: $ " sys.argv[0] " thingy.scm\n")
  (%exit #f -1))

;; I have a feeling some monadish stuff would help here.
(define (get-string-opts given name)
  (match (getopt given name) with
    (maybe:yes (optval:list ovals))
    -> (let ((result '()))
         (for-list oval ovals
           (match oval with
             (optval:string s)
             -> (push! result s)
             _ -> #u
             ))
         (maybe:yes (reverse result)))
    _ -> (maybe:no)
    ))

(define (main)
  (define formals->tenv
    env ()                        -> env
    env ((aztname:t x tx _) . tl) -> (formals->tenv (alist:entry x tx env) tl)
    )
  (let ((opts (get-options))
        (quiet? #f)
        (eval? #f)
        (rewrite? #t)
        (paths '()))
    (when-maybe v (get-bool-opt opts 'eval)
      (set! eval? #t))
    (when-maybe v (get-bool-opt opts 'nr)
      (set! rewrite? #f))
    (when-maybe v (get-bool-opt opts 'quiet)
      (set! quiet? #t))
    (when-maybe v (get-string-opts opts 'paths)
      (set! paths v))
    ;; prepend our basis.
    (set! paths (list:cons "gaz-basis.scm" (reverse paths)))
    (let ((tops (parse (read-files paths)))
          (tenv (alist:nil))
          (funs '())
          (lits '())
          (compiled '()))
      (for-list top tops
        (match top with
          (ztop:fun (aztname:t name rtype _) formals body)
          -> (begin (alist/push tenv name (ztop->type top)) (push! funs top))
          (ztop:lit (aztname:t name vtype _) val)
          -> (begin (alist/push tenv name vtype) (push! lits (:tuple name vtype val)))
          (ztop:decl name type)
          -> (alist/push tenv name type)
          (ztop:mac _ _ _)
          -> #u ;; probably going away
          ))
      (for-list fun (reverse funs)
        (match (alpha fun tenv) with
          (ztop:fun (aztname:t fname ftype fsrc) formals body)
          -> (let ((tenv0 (formals->tenv tenv formals))
                   (_ (dump-azexp 0 body))
                   (_ (printf "\nref-ref...\n"))
                   (body0 (ref-ref tenv0 body))
                   (_ (dump-azexp 0 body0))
                   (_ (printf "\nsolve types (zexp)...\n"))
                   (_ (solve-zexp tenv0 body0))
                   (_ (dump-azexp 0 body0))
                   (_ (printf "\nzexp->cps...\n"))
                   (cps0 (zexp->cps tenv0 body0))
                   (_ (printf "\ncps0:\n"))
                   (_ (dump-cps 0 cps0))
                   (_ (printf "early solve...\n"))
                   (_ (solve tenv (alist:entry 'halt (list ftype) (alist:nil)) cps0))
                   (_ (printf "rewrite...\n"))
                   (cps1 (if rewrite? (rewrite-cps cps0) cps0))
                   )
               ;; (printf "\ncps0:\n")
               ;; (dump-cps 0 cps0)
               (printf "\ncps1:\n")
               (dump-cps 0 cps1)
               (solve tenv (alist:entry 'halt (list ftype) (alist:nil)) cps1)
               (printf "\ndefault-vec-index...\n")
               (default-vec-index cps1 (type:int (itype:fix 32)))
               (let ((cps2 (cps-subst cps1))
                     (cps3 (strip-void cps2)))
                 (printf "\n" (bold (sym fname)) " typed (& stripped):\n")
                 (dump-cps 0 cps3)
                 (push! compiled (:tuple fname ftype formals cps3))
                 ))
          _
          -> #u
          ))
      (if eval?
          (eval tenv compiled lits quiet?)
          (compiled->llvm (last paths) tenv (reverse compiled) lits))
      )))

(main)

