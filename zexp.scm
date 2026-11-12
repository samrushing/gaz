;; -*- Mode: Irken -*-

;; ----- gaz datatypes -----

(typealias zsrc {path=string line=int pos=int})
(define null-zsrc {path="null" line=-1 pos=-1})

;; zexp annotated with src location.
(datatype azexp
  (:t zexp zsrc type)
  )

(define (azexp exp src)
  (azexp:t exp src (new-tvar))
  )

(define azexp/exp
  (azexp:t exp _ _) -> exp
  )
(define azexp/src
  (azexp:t _ src _) -> src
  )
(define azexp/type
  (azexp:t _ _ typ) -> typ
  )

;; name:type pair with src location.
(datatype aztname
  (:t symbol type zsrc)
  )

(define aztname/name
  (aztname:t name _ _) -> name
  )
(define aztname/type
  (aztname:t _ type _) -> type
  )
(define aztname/src
  (aztname:t _ _ src) -> src
  )

;; gaz literal
(datatype zlit
  (:none)
  (:big big)
  (:vec (vector zlit))
  )

;; gaz expression
(datatype zexp
  (:lit zlit)                          ;; value
  (:prim symbol sexp (list azexp))     ;; name param args
  (:seq (list azexp))                  ;; exp ...
  (:let aztname azexp azexp)           ;; name:type init body
  (:varref symbol)                     ;; name
  (:if azexp azexp azexp)              ;; test con alt
  (:call symbol (list azexp))          ;; name args
  (:loop symbol                        ;; name
         (list (:tuple aztname azexp)) ;; (name:type init)+
         azexp)                        ;; body
  (:letcont symbol (list aztname)      ;; Kname args K L
            azexp azexp)
  (:appk symbol (list azexp))          ;; kname arg
  )

;; gaz top-level object
(datatype ztop
  (:fun aztname (list aztname) azexp) ;; name formals body
  (:decl symbol type)                 ;; name type
  (:lit aztname zlit)                 ;; name value
  ;; XXX probably not needed.
  (:mac symbol zsrc                    ;; name src patterns
        (list (:tuple sexpat sexpat)
              ))
  )

;; XXX remove this fun
(define ztop->type
  (ztop:fun (aztname:t fname rtype _) formals _)
  -> (type:arrow rtype (map aztname/type formals))
  (ztop:decl name type)
  -> type
  (ztop:lit (aztname:t name type src) val)
  -> type
  (ztop:mac _ _ _)
  -> none
  )

(define indent-src
  src depth type
  -> (printf
      (ansi green "\n[" (lpad 4 (int src.line))
            (lpad 4 (int src.pos)) "] "
            (lpad 20 (type-repr (apply-subst type))) " "
            (repeat depth "  "))))

(define dump-azexp
  d (azexp:t exp src type)
  -> (begin (indent-src src d type) (dump-zexp d exp))
  )

(define format-aztname
  (aztname:t name ztype src)
  -> (format (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp ztype))))
  )

(define dump-azbind
  d (:tuple name init)
  -> (begin
       (indent-src (aztname/src name) d (aztname/type name))
       (printf (format-aztname name))
       (dump-azexp (+ d 1) init)
       )
  )

(define zlit-repr
  (zlit:none)     -> "none"
  (zlit:big n)    -> (big->dec n)
  (zlit:vec subs) -> (format "#(" (join zlit-repr " " (vector->list subs)) ")")
  )

(define zlit->sexp
  (zlit:none)     -> (sexp:undef null-src)
  (zlit:big n)    -> (sexp (sym '%int) (int 10) (string (big->dec n)))
  (zlit:vec subs) -> (sexp:vector (map zlit->sexp (vector->list subs)) null-src)
  )

(define zlit-zero?
  (zlit:big (big:zero)) -> #t
  _                     -> #f
  )

;; this will get more complicated if we expand the `src` datatype.
(define parse-%ann
  (sexp:list ((sexp:symbol 'src _) (sexp:string path _) (sexp:int line _) (sexp:int pos _)) _)
  -> {path=path line=line pos=pos}
  _
  -> null-zsrc
  )

(define dump-ztop
  (ztop:fun (aztname:t fname ftype fsrc) formals body)
  -> (begin
       (indent-src fsrc 0 ftype)
       (printf "define " (ansi cyan (sym fname)) ":" (ansi yellow (repr (type->sexp ftype))))
       (for-list formal formals
         (match formal with
           (aztname:t name ztype src)
           -> (begin
                (indent-src src 1 ztype)
                (printf (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp ztype)))))
           ))
       (dump-azexp 2 body))
  (ztop:decl name type)
  -> (begin
       (indent-src null-zsrc 0 type)
       (printf "declare " (ansi cyan (sym name)) " " (repr (type->sexp type))))
  (ztop:lit (aztname:t name type src) val)
  -> (begin
       (indent-src src 0 type)
       (printf "define " (ansi cyan (sym name))
               ":" (ansi yellow (repr (type->sexp type)))
               " " (zlit-repr val)))
  (ztop:mac name src pats)
  -> (begin
       (indent-src src 0 (type:none))
       (printf "defmacro " (ansi cyan (sym name)))
       (for-list pat pats
         (match pat with
           (:tuple (sexpat:ann isrc ipat) (sexpat:ann osrc opat))
           -> (begin
                (indent-src (parse-%ann isrc) 1 (type:none))
                (printf (sexpat-repr ipat) (ansi yellow " -> ") (sexpat-repr opat)))
           _ -> (raise (:UnAnnotatedPatterns pat))
           )))
  )

;; demonstrates that we have correctly annotated every sub-expression.
(define dump-zexp
  d (zexp:lit lit)
  -> (printf "lit " (zlit-repr lit))
  d (zexp:prim name param exps)
  -> (begin
       (printf "prim " (ansi cyan (sym name)) " " (repr param))
       (for-list exp exps
         (dump-azexp (+ d 1) exp)))
  d (zexp:varref name)
  -> (printf "varref " (ansi cyan (sym name)))
  d (zexp:seq exps)
  -> (begin
       (printf "begin")
       (for-list exp exps
         (dump-azexp (+ d 1) exp)))
  d (zexp:if b t f)
  -> (begin
       (printf "if")
       (dump-azexp (+ d 1) b)
       (dump-azexp (+ d 1) t)
       (dump-azexp (+ d 1) f))
  d (zexp:appk name exps)
  -> (begin
       (printf "appk " (ansi cyan (sym name)))
       (for-list exp exps
         (dump-azexp (+ d 1) exp)))
  d (zexp:call name exps)
  -> (begin
       (printf "call " (ansi cyan (sym name)))
       (for-list exp exps
         (dump-azexp (+ d 1) exp)))
  d (zexp:let (aztname:t name zt src) init body)
  -> (begin
       (printf "let " (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp zt)))
               " [" (int src.line) "." (int src.pos) "]")
       (dump-azexp (+ d 1) init)
       (dump-azexp (+ d 1) body))
  d (zexp:loop name binds body)
  -> (begin
       (printf "loop " (ansi cyan (sym name)))
       (for-list bind binds
         (dump-azbind (+ d 1) bind))
       (dump-azexp (+ d 1) body))
  d (zexp:letcont Kname args K L)
  -> (begin
       (printf "letcont " (ansi cyan (sym Kname)) " "
               (join format-aztname " " args))
       (dump-azexp (+ d 1) K)
       (dump-azexp d L))
  )

;;
;; run (p walk src env type zexp) over exp.
;;
;; your procedure `p` makes the decision of when/how to continue
;;   walking the expression.

(define (walk-zexp tenv exp p)

  (define extend
    env (aztname:t name type src) -> (alist:entry name type env)
    )

  (define extend*
    env ()        -> env
    env (hd . tl) -> (extend* (extend env hd) tl)
    )

  ;; remove, process, and restore annotation.
  (define W
    env (azexp:t exp src type)
    -> (azexp:t (p W0 src env type exp) src type)
    )

  (define W*
    acc env ()        -> (reverse acc)
    acc env (hd . tl) -> (W* (list:cons (W env hd) acc) env tl)
    )

  (define W0
    env (zexp:lit v)       -> (zexp:lit v)
    env (zexp:varref n)    -> (zexp:varref n)
    env (zexp:prim n p xs) -> (zexp:prim n p (W* '() env xs))
    env (zexp:seq xs)      -> (zexp:seq (W* '() env xs))
    env (zexp:if t c a)    -> (zexp:if (W env t) (W env c) (W env a))
    env (zexp:appk n xs)   -> (zexp:appk n (W* '() env xs))
    env (zexp:call n xs)   -> (zexp:call n (W* '() env xs))
    env (zexp:let n i b)   -> (zexp:let n (W env i) (W (extend env n) b))
    env (zexp:letcont n names k l)
    -> (let ((env0 (extend* env names)))
         (zexp:letcont n names (W env0 k) (W env0 l)))
    env (zexp:loop n binds body)
    -> (let (((names inits) (unzip binds))
             (env0 (extend* env names)))
         (zexp:loop n
                    (zip names (W* '() env0 inits))
                    (W env0 body)))
    )

  (W tenv exp)
  )

;; ref-ref: convert (varref x:(ref T)) into (%get x)

(define (ref-ref env exp)

  (define convert
    ;; don't convert an lval!
    walk src env type (zexp:prim '%set! param (lval (azexp:t x xsrc tx)))
    -> (zexp:prim '%set! param (list lval (azexp:t (walk env x) xsrc tx)))

    ;; don't convert an asref
    walk src env type (zexp:prim '%asref param ((azexp:t x xsrc tx)))
    -> x

    walk src env type (zexp:varref n)
    -> (match (alist/lookup env n) with
         ;; leave (ref (vec ...)) alone.
         (maybe:yes (type:ref (type:vec _ _ _)))
         -> (zexp:varref n)
         (maybe:yes (type:mut (type:vec _ _ _)))
         -> (zexp:varref n)
         ;; is this a ref type? if so, replace it with (%get x)
         (maybe:yes (type:ref t))
         -> (zexp:prim '%get (sexp:undef null-src) (list (azexp:t (zexp:varref n) src (new-tvar))))
         (maybe:yes (type:mut t))
         -> (zexp:prim '%get (sexp:undef null-src) (list (azexp:t (zexp:varref n) src (new-tvar))))
         _
         -> (zexp:varref n)
         )
    walk src env type exp
    -> (walk env exp)
    )

  (walk-zexp env exp convert)

  )


