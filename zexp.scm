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
  (:vec (list zlit))
  )

;; gaz expression
(datatype zexp
  (:lit zlit)                          ;; value
  (:prim symbol sexp (list azexp))     ;; name param args
  (:seq (list azexp))                  ;; exp ...
  (:let aztname azexp azexp)           ;; name:type init body
  (:ref symbol)                        ;; name
  ;;(:set symbol azexp)                ;; name value
  (:if azexp azexp azexp)              ;; test con alt
  (:call symbol (list azexp))          ;; name args
  (:loop symbol                        ;; name
         (list (:tuple aztname azexp)) ;; (name:type init)+
         azexp)                        ;; body
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
  -> (type/arrow rtype (map aztname/type formals))
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
  d (azexp:t exp src) -> (begin (indent-src src d) (dump-zexp d exp))
  )

(define dump-azbind
  d (:tuple (aztname:t name ztype src) init)
  -> (begin
       (indent-src src d)
       (printf (ansi cyan (sym name)) ":" (ansi yellow (repr (type->sexp ztype))))
       (dump-azexp (+ d 1) init)
       )
  )

(define zlit-repr
  (zlit:int n)
  -> (format (int n))
  (zlit:vec subs)
  -> (format "#(" (join zlit-repr " " subs) ")")
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
       (dump-azexp 2 body)
       )
  (ztop:decl name type)
  -> (begin
       (indent-src null-src 0)
       (printf "declare " (ansi cyan (sym name)) " " (repr (type->sexp type)))
       )
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
  ;; d (zexp:set name exp)
  ;; -> (begin
  ;;      (printf "set " (ansi cyan (sym name)))
  ;;      (dump-azexp (+ d 1) exp))
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
  )
