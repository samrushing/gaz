;; -*- Mode: Irken -*-

;; ----- gaz datatypes -----

(typealias src {path=string line=int pos=int})
(define null-src {path="null" line=-1 pos=-1})

;; zexp annotated with src location.
(datatype azexp
  (:t zexp src)
  )

(define azexp/exp
  (azexp:t exp _) -> exp
  )
(define azexp/src
  (azexp:t _ src) -> src
  )

;; name:type pair with src location.
(datatype aztname
  (:t symbol type src)
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
  (:int int)
  (:big big)
  (:vec (vector zlit))
  )

;; gaz expression
(datatype zexp
  (:lit zlit)                          ;; value
  (:prim symbol sexp (list azexp))     ;; name param args
  (:seq (list azexp))                  ;; exp ...
  (:let aztname azexp azexp)           ;; name:type init body
  (:ref symbol)                        ;; name
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
  (:mac symbol src                    ;; name src patterns
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
  src depth -> (printf
                (ansi green "\n[" (lpad 4 (int src.line))
                      (lpad 4 (int src.pos)) "]  " (repeat depth "  "))))

(define dump-azexp
  d (azexp:t exp src)
  -> (begin (indent-src src d) (dump-zexp d exp))
  )

(define format-aztname
  (aztname:t name ztype src)
  -> (format (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp ztype))))
  )

(define dump-azbind
  d (:tuple name init)
  -> (begin
       (indent-src (aztname/src name) d)
       (printf (format-aztname name))
       (dump-azexp (+ d 1) init)
       )
  )

(define zlit-repr
  (zlit:int n)    -> (format (int n))
  (zlit:big n)    -> (big->dec n)
  (zlit:vec subs) -> (format "#(" (join zlit-repr " " (vector->list subs)) ")")
  )

(define zlit->sexp
  (zlit:int n)    -> (sexp (sym '%int) (int 10) (string (int->string n)))
  (zlit:big n)    -> (sexp (sym '%int) (int 10) (string (big->dec n)))
  (zlit:vec subs) -> (sexp:vector (map zlit->sexp (vector->list subs)))
  )

(define zlit-zero?
  (zlit:int 0)          -> #t
  (zlit:big (big:zero)) -> #t
  _                     -> #f
  )

;; this will get more complicated if we expand the `src` datatype.
(define parse-%ann
  (sexp:list ((sexp:symbol 'src) (sexp:string path) (sexp:int line) (sexp:int pos)))
  -> {path=path line=line pos=pos}
  _
  -> null-src
  )

(define dump-ztop
  (ztop:fun (aztname:t fname ftype fsrc) formals body)
  -> (begin
       (indent-src fsrc 0)
       (printf "define " (ansi cyan (sym fname)) ":" (ansi yellow (repr (type->sexp ftype))))
       (for-list formal formals
         (match formal with
           (aztname:t name ztype src)
           -> (begin
                (indent-src src 1)
                (printf (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp ztype)))))
           ))
       (dump-azexp 2 body))
  (ztop:decl name type)
  -> (begin
       (indent-src null-src 0)
       (printf "declare " (ansi cyan (sym name)) " " (repr (type->sexp type))))
  (ztop:lit (aztname:t name type src) val)
  -> (begin
       (indent-src src 0)
       (printf "define " (ansi cyan (sym name))
               ":" (ansi yellow (repr (type->sexp type)))
               " " (zlit-repr val)))
  (ztop:mac name src pats)
  -> (begin
       (indent-src src 0)
       (printf "defmacro " (ansi cyan (sym name)))
       (for-list pat pats
         (match pat with
           (:tuple (sexpat:ann isrc ipat) (sexpat:ann osrc opat))
           -> (begin
                (indent-src (parse-%ann isrc) 1)
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
  d (zexp:ref name)
  -> (printf "ref " (ansi cyan (sym name)))
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

;; these belong in lib/pair.scm

(define (unzip pairs)
  (define U
    acc0 acc1 ()                    -> (:tuple (reverse acc0) (reverse acc1))
    acc0 acc1 ((:tuple a b) . rest) -> (U (list:cons a acc0) (list:cons b acc1) rest)
    )
  (U (list:nil) (list:nil) pairs))

(define (zip as bs)
  (define Z
    acc () ()             -> (reverse acc)
    acc (a . as) (b . bs) -> (Z (list:cons (:tuple a b) acc) as bs)
    acc _ _               -> (raise (:Zip/UnequalLengthLists))
    )
  (Z '() as bs)
  )

;;
;; run (p walk src env zexp) over exp.
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
    env (azexp:t exp src)
    -> (azexp:t (p W0 src env exp) src)
    )

  (define W*
    acc env ()        -> (reverse acc)
    acc env (hd . tl) -> (W* (list:cons (W env hd) acc) env tl)
    )

  (define W0
    env (zexp:lit v)       -> (zexp:lit v)
    env (zexp:ref n)       -> (zexp:ref n)
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
    walk src env (zexp:ref n)
    -> (match (alist/lookup env n) with
         ;; leave (ref (vec ...)) alone.
         (maybe:yes (type:ref (type:vec _ _)))
         -> (zexp:ref n)
         ;; is this a ref type? if so, replace it with (%get x)
         (maybe:yes (type:ref t))
         -> (zexp:prim '%get (sexp:undef) (list (azexp:t (zexp:ref n) src)))
         _
         -> (zexp:ref n)
         )
    walk src env exp
    -> (walk env exp)
    )

  (walk-zexp env exp convert)

  )


