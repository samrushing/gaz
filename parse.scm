;; -*- Mode: Irken -*-

(require "lib/bignum.scm")
(require "./pp.scm")

;; Note: this is really our first-pass parser, and will be detecting the most
;;  common syntax errors.  So we'll need to handle those cleanly _here_.

;; [here is where we might handle <srcs>.
;; we might want the 'src' datatype to have 3 arms:
;;
;; (datatype src
;;   (:one src-rec)
;;   (:many (list src-rec))
;;   (:none)
;;   )
;;
;; perhaps even more useful: rather than including a list
;;   of the src locations of macro expansions, we could include
;;   the _name_ of the macro that caused that expansion?  How useful
;;   is the exact location in a macro ipat/opat? [somewhat, honestly]
;;   regardless, the name of the macro would be some sweet metadata.
;;
;; so maybe something like this instead:
;;
;; (datatype src
;;   (:t src-rec)
;;   (:macro symbol src-rec src) ;; ie a chain.
;;   (:none)
;;   )

(define sexp->src
  (sexp:list ((sexp:symbol 'src) (sexp:string path) (sexp:int line) (sexp:int pos)))
  -> {path=path line=line pos=pos}
  _
  -> null-src
  )

(define (imp)
  (raise (:Impossible)))

(define unpack-ann
  (sexp:list ((sexp:symbol '%ann) ann exp))
  -> (:tuple ann exp)
  exp
  -> (:tuple (sexp:undef) exp)
  )

(define (ann-list? exp)
  (match (unpack-ann exp) with
    (:tuple ann (sexp:list exps)) -> (maybe:yes (:tuple ann exps))
    otherwise                     -> (maybe:no)
    ))

(define (ann-symbol? exp)
  (match (unpack-ann exp) with
    (:tuple ann (sexp:symbol sym)) -> (maybe:yes (:tuple ann sym))
    otherwise                      -> (maybe:no)
    ))

;; apply all known macros to <exp>.
;; this carefully unwraps and rewraps src annotations,
;;   while also handling the annotations added by macro/expand.
;;
;; currently we are collapsing overlapping annotations into a
;;   single annotation but I plan to do the above solution where
;;   we keep the extras, but perhaps with metadata about which
;;   macro added them.

(define (transform menv exp)

  (define (wrap-ann ann exp)
    (sexp (sym '%ann) ann exp))

  (define (walk exp)
    (match (ann-list? exp) with
      (maybe:yes (:tuple ann0 (hd . tl)))
      -> (match (ann-symbol? hd) with
           (maybe:yes (:tuple ann1 sym))
           -> (match (alist/lookup menv sym) with
                ;; XXX detect runaway expansion here.
                (maybe:yes macro)
                -> (walk (keep-one-annotation (macro/expand macro exp)))
                (maybe:no)
                -> (match (alist/lookup core-forms sym) with
                     (maybe:yes fun)
                     -> (fun ann0 hd tl)
                     (maybe:no)
                     -> (wrap-ann ann0 (sexp:list (list:cons hd (map walk tl))))
                     ))
           (maybe:no)
           ;; non-symbol operator
           -> (wrap-ann ann0 (sexp:list (map walk (list:cons hd tl))))
           )
      ;; empty (annotated) list
      (maybe:yes (:tuple ann0 ()))
      -> exp
      ;; non-list element
      (maybe:no)
      -> exp
      ))

  (define (walk-all ann hd tl)
    (wrap-ann ann (sexp:list (list:cons hd (map walk tl)))))

  (define (walk-let-loop ann hd tl)
    ;; (let-loop name ((name:type init) ...) exp)
    (match tl with
      (name bindings exp)
      -> (wrap-ann
          ann
          (sexp:list
           (list hd name (walk-bindings ann bindings) (walk exp))))
      _
      -> (raise (:SyntaxError ann (sexp:list (list:cons hd tl))))
      ))

  (define (walk-bindings ann bindings)
    (match (ann-list? bindings) with
      (maybe:yes (:tuple ann0 bindings0))
      -> (wrap-ann ann0 (sexp:list (walk-bindings* (list:nil) ann0 bindings0)))
      (maybe:no)
      -> (raise (:SyntaxError ann bindings))
      ))

  ;; rewrite as a fold?
  (define walk-bindings*
    acc ann ()             -> (reverse acc)
    acc ann (bind . binds) -> (walk-bindings*
                               (list:cons (walk-binding ann bind) acc)
                               ann
                               binds))

  (define (walk-binding ann bind)
    (match (ann-list? bind) with
      ;; XXX parse/verify name-type here?
      (maybe:yes (:tuple ann0 (name-type init)))
      -> (wrap-ann ann0 (sexp name-type (walk init)))
      otherwise
      -> (raise (:SyntaxError ann bind))
      ))

  (define (walk-prim ann hd tl)
    (match tl with
      (name-type param . args)
      -> (wrap-ann
          ann
          (sexp:list
           (append (list hd name-type (remove-annotations param))
                   (map walk args))))
      tl
      -> (raise (:SyntaxError ann (sexp:list tl)))
      ))

  (define (walk-let-val ann hd tl)
    ;; (%let-val name:type init body)
    (match tl with
      (name-type init body)
      -> (wrap-ann ann (sexp hd name-type (walk init) (walk body)))
      _
      -> (raise (:SyntaxError ann (sexp:list tl)))
      ))

  (define (walk-let-cont ann hd tl)
    ;; (%let-cont Kname (name:type ...) K L)
    (match tl with
      (Kname vars K L)
      -> (wrap-ann ann (sexp hd Kname vars (walk K) (walk L)))
      otherwise
      -> (raise (:SyntaxError ann (sexp:list tl)))
      ))

  ;; this is actually a no-op.
  (define (walk-int ann hd tl)
    (wrap-ann ann (sexp:list (list:cons hd tl)))
    )

  (define core-forms
    (alist/make
     ('%begin    walk-all)
     ('%if       walk-all)
     ('%appk     walk-all)
     ('%let-val  walk-let-val)
     ('%let-loop walk-let-loop)
     ('%let-cont walk-let-cont)
     ('%prim     walk-prim)
     ('%int      walk-int)
     ))

  (try
   (walk exp)
   except
   (:SyntaxError src exp)
   -> (begin
        (printf (bold "Syntax Error: " (repr src) "\n"))
        (dump-ann-sexp 0 exp)
        (printf "\n")
        (%exit #f -1)
        )
   )
  )

(define null-ann (sexp (sym 'src) (string "null") (int 0) (int 0)))

;; I think the _right_ way to do this is to introduce a new type of annotation,
;;   that includes multiple src entries.  Probably <srcs>.
;; But this will do for now!

(define (keep-one-annotation exp)

  (define D
    ann0 (sexp:list ((sexp:symbol '%ann) ann exp))
    -> (D ann exp)
    ann0 (sexp:list exps)
    -> (sexp (sym '%ann) ann0 (list (map (partial (D ann0 _)) exps)))
    ann0 exp
    -> (sexp (sym '%ann) ann0 exp)
    )

  (D null-ann exp)
  )

(define dump-sexp
  d (sexp:list (hd . tl))
  -> (begin
       (printf "(")
       (dump-ann-sexp (+ d 1) hd)
       (for-list exp tl
         (dump-ann-sexp (+ d 1) exp))
       (printf ")")
       )
  d exp
  -> (printf (repr exp))
  )

(define dump-ann-sexp
  d (sexp:list
     ((sexp:symbol '%ann)
      (sexp:list ((sexp:symbol 'src)
                  (sexp:string path)
                  (sexp:int line)
                  (sexp:int pos)))
      exp))
  -> (begin
       (printf "\n[" (lpad 3 (int line)) ":" (lpad 3 (int pos)) "]" (repeat d "  "))
       (dump-ann-sexp d exp))
  d exp
  -> (dump-sexp d exp)
  )


;; ----- parser -----

;; core expressions:
;;
;; (%begin exp ...)
;; (%let-val name:type init body)
;; (%let-loop name ((name:type init) ...) body)
;; (%set! name exp)  [note: probably a prim]
;; (%if exp exp exp)
;; (%appk name exp ...)
;; (%prim name param exp ...)
;; (exp exp ...)

(define (parse* exps)

  (define core-forms
    (alist/make
     ('%begin    walk-begin)
     ('%if       walk-if)
     ('%prim     walk-prim)
     ('%let-val  walk-let-val)
     ('%let-loop walk-let-loop)
     ('%let-cont walk-let-cont)
     ('%appk     walk-appk)
     ('%int      walk-int)
     ))

  ;; XXX I think a bunch of this boilerplate can be shrunk by
  ;;  using something like `expect-symbol`, `expect-form`, which
  ;;  could throw the necessary syntax errors in one place.
  ;;  [probably applies to `transform` as well]

  ;; sexp->azexp

  (define (walk exp)
    (match (ann-list? exp) with
      (maybe:yes (:tuple ann0 (hd . tl)))
      -> (match (ann-symbol? hd) with
           (maybe:yes (:tuple ann1 sym))
           -> (match (alist/lookup core-forms sym) with
                (maybe:yes fun)
                -> (fun ann0 tl)
                (maybe:no)
                -> (walk-app ann0 sym tl)
                )
           (maybe:no)
           ;; non-symbol operator
           -> (raise (:SyntaxError ann0 (sexp:list (list:cons hd tl))))
           )
      ;; empty (annotated) list  (probably a syntax error)
      (maybe:yes (:tuple ann0 ()))
      -> (raise (:SyntaxError ann0 (sexp:list '())))
      ;; non-list element
      (maybe:no)
      -> (walk-atom exp)
      ))

  (define (walk-app ann op args)
    (azexp:t (zexp:call op (map walk args)) (sexp->src ann)))

  (define (walk-atom exp)
    (match (unpack-ann exp) with
      (:tuple ann exp0)
      -> (match exp0 with
           (sexp:int n)
           -> (azexp:t (zexp:lit (zlit:int n)) (sexp->src ann))
           (sexp:vector subs)
           -> (azexp:t (zexp:lit (sexp->zlit ann exp0)) (sexp->src ann))
           (sexp:symbol var)
           -> (azexp:t (zexp:ref var) (sexp->src ann))
           exp
           -> (raise (:SyntaxError ann exp))
           )))

  (define (walk-begin ann exps)
    (azexp:t (zexp:seq (map walk exps)) (sexp->src ann)))

  (define walk-if
    ann (tst con alt)
    -> (azexp:t (zexp:if (walk tst) (walk con) (walk alt)) (sexp->src ann))
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define walk-prim
    ann (name param . args)
    -> (match (unpack-ann name) (unpack-ann param) with
         (:tuple ann0 (sexp:symbol name)) (:tuple ann1 param)
         -> (azexp:t (zexp:prim name param (map walk args)) (sexp->src ann))
         _ _
         -> (raise (:SyntaxError ann name)) ;; cop-out, really
         )
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define (walk-type ann exp)
    (try
     (parse-type (remove-annotations exp))
     except
     (:ParseTypeFailed _)
     -> (raise (:SyntaxError ann exp))
     ))

  (define (parse-name-type ann name-type)
    (match (unpack-ann name-type) with
      (:tuple ann0 (sexp:list (typed name type)))
      -> (match (unpack-ann typed) (unpack-ann name) (unpack-ann type) with
           ;; e.g. (%typed x i32)
           (:tuple _ (sexp:symbol '%typed))
           (:tuple ann2 (sexp:symbol name0))
           (:tuple ann3 type-expr)
           -> (aztname:t name0 (walk-type ann3 type-expr) (sexp->src ann0))
           _ _ _
           -> (raise (:SyntaxError ann name-type))
           )
      _
      -> (raise (:SyntaxError ann name-type))
      ))

  (define walk-let-val
    ann (name-type init body)
    -> (azexp:t
        (zexp:let
         (parse-name-type ann name-type)
         (walk init)
         (walk body))
        (sexp->src ann))
    ann exps
    -> (raise (:SyntaxError ann (sexp:list exps)))
    )

  (define (walk-bindings ann bindings)
    (match (ann-list? bindings) with
      (maybe:yes (:tuple ann0 bindings0))
      -> (walk-bindings* (list:nil) ann0 bindings0)
      (maybe:no)
      -> (raise (:SyntaxError ann bindings))
      ))

  (define walk-bindings*
    acc ann ()             -> (reverse acc)
    acc ann (bind . binds) -> (walk-bindings*
                               (list:cons (walk-binding ann bind) acc)
                               ann
                               binds))

  (define (walk-binding ann bind)
    (match (ann-list? bind) with
      (maybe:yes (:tuple ann0 (name-type init)))
      -> (:tuple (parse-name-type ann0 name-type) (walk init))
      _
      -> (raise (:SyntaxError ann bind))
      ))

  (define walk-let-loop
    ann (name bindings body)
    -> (match (unpack-ann name) with
         (:tuple ann0 (sexp:symbol name))
         -> (azexp:t
             (zexp:loop name
                        (walk-bindings ann bindings)
                        (walk body))
             (sexp->src ann))
         (:tuple ann0 other)
         -> (raise (:SyntaxError ann0 other))
         )
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define walk-let-cont
    ann (Kname vars K L)
    -> (match (unpack-ann Kname) (unpack-ann vars) with
         (:tuple ann0 (sexp:symbol Kname0)) (:tuple ann1 (sexp:list vars0))
         -> (azexp:t
             (zexp:letcont
              Kname0
              (map (partial (parse-name-type ann _)) vars0)
              (walk K)
              (walk L))
             (sexp->src ann))
         _ _
         -> (raise (:SyntaxError ann (sexp Kname vars K L)))
         )
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define walk-appk
    ann (name . args)
    -> (match (unpack-ann name) with
         (:tuple ann0 (sexp:symbol name))
         -> (azexp:t
             (zexp:appk name (map walk args))
             (sexp->src ann))
         _
         -> (raise (:SyntaxError ann (sexp:list (list:cons name args))))
         )
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define big->zlit
    ann ((sexp:int base) (sexp:string digits))
    -> (zlit:big (literal->big base digits))
    ann other
    -> (raise (:SyntaxError ann (sexp:list other)))
    )

  (define (walk-int ann lit)
    (azexp:t (zexp:lit (big->zlit ann (map remove-annotations lit)))
             (sexp->src ann)))

  ;; ----- top-level -----

  ;; * something missing from irken: macro scope.  It would
  ;;   be nice to have lexically-scoped macros.
  ;;   what's the right way to do that?  If we consider the
  ;;   top-level to be a scope/body, then we can have a generic
  ;;   <body> that handles all various scoping.  would lits have
  ;;   global scope?  would we use scope prefixes?

  ;; first-pass version (no macro scopes):
  ;; 1) collect all the macros
  ;; 2) apply transform to everything not a macro.
  ;;   [what if we produce new macros!?]
  ;; 3) cps, opt, llvm

  ;; fun/decl/lit/mac

  (define (partition-forms exps symbol)
    (define PF
      p acc0 acc1 () -> (:tuple (reverse acc0) (reverse acc1))
      p acc0 acc1 (hd . tl)
      -> (match (p hd) with
           (:tuple #t val) -> (PF p (list:cons val acc0) acc1 tl)
           (:tuple #f val) -> (PF p acc0 (list:cons val acc1) tl)
           ))
    (PF (partial (is-form? _ symbol)) '() '() exps)
    )

  (define (is-form? exp name)
    (match (ann-list? exp) with
      (maybe:yes (:tuple ann0 (hd . tl)))
      -> (match (ann-symbol? hd) with
           (maybe:yes (:tuple ann1 sym))
           -> (if (sexp=? sym name)
                  ;; IF it's a match, deliver the un-annotated tail as payload.
                  (:tuple #t (:tuple ann0 (sexp:list tl)))
                  (:tuple #f (:tuple ann0 exp)))
           (maybe:no)
           -> (:tuple #f (:tuple ann0 exp)))
      _
      -> (match (unpack-ann exp) with
           (:tuple ann exp0)
           -> (raise (:SyntaxError ann exp0)))
      ))

  (define (parse-macro macro)
    (match macro with
      (:tuple ann (sexp:list (name . pairs)))
      -> (match (ann-symbol? name) with
           (maybe:yes (:tuple ann0 name))
           -> (:tuple name (macro/parse pairs))
           (maybe:no)
           ;;-> (raise (:SyntaxError ann (sexp:list (list:cons name pairs))))
           -> (raise (:SyntaxError ann name))
           )
      (:tuple ann exps)
      -> (raise (:SyntaxError ann exps))
      ))

  ;; (declare <name> <type>)
  (define (parse-decl ann exps)
    (match exps with
      (name type)
      -> (match (ann-symbol? name) with
           (maybe:yes (:tuple ann0 name))
           -> (:tuple name (ztop:decl name (parse-type (remove-annotations type))))
           (maybe:no)
           -> (raise (:SyntaxError ann (sexp name type)))
           )
      _
      -> (raise (:SyntaxError ann (sexp:list exps)))
      ))

  ;; again with the code duplication...
  (define (parse-toplevel exp)
    (match (ann-list? exp) with
      (maybe:yes (:tuple ann0 (hd . tl)))
      -> (match (ann-symbol? hd) with
           (maybe:yes (:tuple ann1 sym))
           -> (match sym with
                '%declare -> (parse-decl ann0 tl)
                '%define  -> (parse-fun ann0 tl)
                '%deflit  -> (parse-lit ann0 tl)
                _ -> (raise (:SyntaxError ann0 exp))
                )
           (maybe:no)
           -> (raise (:SyntaxError ann0 exp))
           )
      _
      -> (match (unpack-ann exp) with
           (:tuple ann exp0)
           -> (raise (:SyntaxError ann exp0)))
      ))

  ;; (%define name-type (arg ...) body)
  (define (parse-fun ann exps)
    (match exps with
      (name-type formals body)
      -> (let ((zname (parse-name-type ann name-type)))
           (match (unpack-ann formals) with
             (:tuple ann (sexp:list formals))
             -> (:tuple (aztname/name zname)
                        (ztop:fun zname
                                  (map (partial (parse-name-type ann _)) formals)
                                  (walk body)))
             _
             -> (raise (:SyntaxError ann formals))
             ))
      _
      -> (raise (:SyntaxError ann (sexp:list exps)))
      ))

  (define (sexp->zlit ann exp)
    (define R
      (sexp:list ((sexp:symbol '%ann) ann exp)) -> (sexp->zlit ann exp)
      (sexp:list ((sexp:symbol '%int) . tl)) -> (big->zlit ann tl)
      (sexp:int n)       -> (zlit:int n)
      (sexp:vector subs) -> (zlit:vec (list->vector (map R subs)))
      other              -> (raise (:SyntaxError ann other))
      )
    (R exp))

  (define (parse-lit ann exps)
    (match exps with
      (name-type litval)
      -> (let ((zname (parse-name-type ann name-type))
               (zlit (sexp->zlit ann litval)))
           (:tuple (aztname/name zname) (ztop:lit zname zlit)))
      _
      -> (raise (:SyntaxError ann (sexp:list exps)))
      ))

  (define (dump-menv menv)
    (for-alist k v menv
      (printf "macro: " (bold (sym k)) "\n")
      (match v with
        (:tuple name pats)
        -> (for-list pat pats
             (match pat with
               (:tuple ipat opat)
               -> (printf "  "
                          (sexpat-repr ipat)
                          (ansi yellow " -> ")
                          (sexpat-repr opat) "\n")
               )))))

  (define (macros->menv macros)
    (define F
      (:tuple name item) acc
      -> (alist:entry name (:tuple name item) acc))
    (foldr F (alist:nil) (map parse-macro macros))
    )

  (let (((macros others) (partition-forms exps 'defmacro))
        (menv (macros->menv macros))
        (tops '()))
    ;; (dump-menv menv)
    (for-list other others
      (match other with
        (:tuple ann exp)
        -> (let ((exp0 (transform menv exp)))
             (pp-src ann exp0 80)
             ;; (dump-ann-sexp 0 exp)
             ;; (printf "\n")
             ;; (dump-ann-sexp 0 exp0)
             ;; (printf "\n")
             ;; (pp exp0 80)
             (let (((name ztop) (parse-toplevel exp0)))
               (push! tops ztop)
               ;;(dump-azexp 0 zexp)
               (dump-ztop ztop)
               (printf "\n"))
             )))
    (printf "done\n")
    (reverse tops)
    ))

(define (parse exps)
  (try
   (parse* exps)
   except
   (:SyntaxError src exp)
   -> (begin
        (printf (bold "Syntax Error: " (repr src) "\n"))
        (pp-src src exp 80)
        ;;(dump-ann-sexp 0 exp)
        (printf "\n")
        (%exit #f -1)
        )
   ))

(define (literal->big base digits)
  (define digits-table
    (alist/make
     (#\0 0) (#\1 1) (#\2 2) (#\3 3) (#\4 4)
     (#\5 5) (#\6 6) (#\7 7) (#\8 8) (#\9 9)
     (#\a 10) (#\b 11) (#\c 12) (#\d 13) (#\e 14) (#\f 15)
     (#\A 10) (#\B 11) (#\C 12) (#\D 13) (#\E 14) (#\F 15)
     ))
  (define (digit->int dig)
    (match (alist/lookup digits-table dig) with
      (maybe:yes val) -> val
      (maybe:no) -> (impossible)
      ))
  (define R
    acc b ()           -> acc
    acc b (dig . digs) -> (R (big (+ (* acc b) (I (digit->int dig)))) b digs)
    )
  (R (big:zero) (int->big base) (string->list digits))
  )

(define (read-files paths)

  (define (read-file path)
    (let ((ifile (file/open-read path))
          (exps (read2 path (lambda () (file/read-char ifile)) #t)))
      (file/close ifile)
      exps))

  ;; probably belongs in lib/pair.scm
  (define flatten
    acc ()        -> (reverse acc)
    acc (hd . tl) -> (flatten (fold list:cons acc hd) tl)
    )

  (flatten '() (map read-file paths))
  )
