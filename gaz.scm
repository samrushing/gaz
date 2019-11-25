;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/cmap.scm")
(require "lib/partial.scm")
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

(define (main)
  (define formals->tenv
    env ()                        -> env
    env ((aztname:t x tx _) . tl) -> (formals->tenv (alist:entry x tx env) tl)
    )
  (let ((paths (rest (vector->list sys.argv)))
        (tops (parse (read-files paths)))
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
                 (body0 (ref-ref tenv body))
                 (cps0 (zexp->cps tenv0 body0))
                 (cps1 (rewrite-cps cps0)))
             (printf "\ncps0:\n")
             (dump-cps 0 cps0)
             (printf "\ncps1:\n")
             (dump-cps 0 cps1)
             (solve tenv (alist:entry 'halt (list ftype) (alist:nil)) cps1)
             ;;(printf "solved\n")
             (let ((cps2 (cps-subst cps1))
                   (cps3 (strip-void cps2)))
               (printf "\n" (bold (sym fname)) " typed (& stripped):\n")
               (dump-cps 0 cps3)
               (push! compiled (:tuple fname ftype formals cps3))
             ))
        _
        -> #u
        ))
    (compiled->llvm (last paths) tenv compiled lits)
    ))

(main)

