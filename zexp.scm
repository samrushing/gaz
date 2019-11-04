;; -*- Mode: Irken -*-

;; ----- gaz datatypes -----

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

;; gaz expression
(datatype zexp
  (:lit int)                         ;; value
  (:prim symbol sexp (list azexp))   ;; name param args
  (:seq (list azexp))                ;; exp ...
  (:let aztname azexp azexp)         ;; name:type init body
  (:ref symbol)                      ;; name
  ;;(:set symbol azexp)                ;; name value
  (:if azexp azexp azexp)            ;; test con alt
  (:call symbol (list azexp))        ;; name args
  (:loop symbol                      ;; name
         (list (:tuple aztname azexp))  ;; (name:type init)+
         azexp)                         ;; body
  (:appk symbol (list azexp))        ;; kname arg
  )

(datatype ztop
  ;;     name      formals    body
  (:fun symbol (list aztname) azexp)
  ;;     name   type
  (:decl symbol type)
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

(define dump-ztop
  (ztop:fun name formals body)
  -> (begin
       (indent-src null-src 0)
       (printf "define " (ansi cyan (sym name)))
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
  )

;; demonstrates that we have correctly annotated every sub-expression.
(define dump-zexp
  d (zexp:lit n)
  -> (printf "lit " (int n))
  d (zexp:prim name param exps)
  -> (begin
       (printf "prim " (ansi cyan (sym name)) (repr param))
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
