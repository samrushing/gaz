;; -*- Mode: Irken -*-

;; used to build useful labels for parser combinators.
(define (wrap-label sym subs)
  (sexp:list
   (list:cons
    (sexp:symbol sym)
    (map (lambda (p) p.label) subs))))

(define (src/if s0 s1)
  (if (eq? s1 null-src) s0 s1))

;; extract src annotation from an s-expression
(define sexp->src
  (sexp:list
   ((sexp:symbol '%ann)
    (sexp:list ((sexp:symbol 'src) (sexp:string path) (sexp:int line) (sexp:int pos)))
    exp))
  -> (:tuple {path=path line=line pos=pos} exp)
  exp
  -> (:tuple null-src exp)
  )

;; this parser expects/extracts annotation info and attaches
;;   it to the result (whether positive or negative).
(define (p-annotated p)
  (define inner
    ()
    -> (result:no null-src p.label "no more input")
    (hd . tl)
    -> (match (sexp->src hd) with
         (:tuple src exp)
         -> (match (p.fun (list exp)) with
              (result:ok src0 val _)
              -> (result:ok (src/if src src0) val tl)
              (result:no src0 label err)
              -> (result:no (src/if src src0) label err)
              (result:fail src0 label err)
              -> (result:fail (src/if src src0) label err)
              ))
    )
  (parser/make inner (sexp (sym 'ann) p.label))
  )

;; like mapP, but passes the src location as an extra arg.
(define (map-ann f parser)
  (let ((label (sexp (sym 'm-ann) parser.label)))
    (parser/make
     (lambda (input)
       (match (parser.fun input) with
         (result:ok src v rest)
         -> (result:ok src (f src v) rest)
         (result:no src _ err)
         -> (result:no src label err)
         (result:fail src lab err)
         -> (result:fail src lab err)
         ))
     label
     )))

;; this is a datatype specifically to help our parser combinators
;; [avoiding the use of polymorphic variants]

(datatype zparse
  (:int int)
  (:bool bool)
  (:sym symbol)
  (:lit sexp)
  (:wild sexp)
  (:opt (maybe zparse))
  (:list (list zparse))
  (:exp azexp)
  (:type type)
  (:tname aztname)
  )

(define (zp-star p) (mapP zparse:list (star p) 'star))
(define (zp-plus p) (mapP zparse:list (plus p) 'plus))
(define (zp-opt p) (mapP zparse:opt (opt p) 'opt))

;; XXX should we have a `maybe` wrapper for these tests?
(define qtest-int
  (sexp:int n) -> (maybe:yes (zparse:int n))
  _            -> (maybe:no)
  )

(define qtest-bool
  (sexp:bool b) -> (maybe:yes (zparse:bool b))
  _             -> (maybe:no)
  )

(define qtest-sym
  (sexp:symbol s) -> (maybe:yes (zparse:sym s))
  _               -> (maybe:no)
  )

;; any s-expression literal
(define (qtest-lit lit)
  (lambda (exp)
    ;;(printf "sexp=? " (repr lit) " - " (repr exp) " " (bool (sexp=? exp lit)) "\n")
    (if (sexp=? exp lit)
        (maybe:yes (zparse:lit lit))
        (maybe:no))))

(define qtest-wild
  exp -> (maybe:yes (zparse:wild exp))
  )

(define (q-satisfy tester label0)
  (define label (sexp:symbol label0))
  (define inner
    ()
    -> (result:no null-src label "no more input")
    (exp . rest)
    -> (match (tester exp) with
         (maybe:yes v) -> (result:ok null-src v rest)
         (maybe:no)    -> (result:no null-src label "unexpected expression type")
         ))
  (parser/make inner label)
  )

(define q-int (q-satisfy qtest-int 'int))
(define qa-int (p-annotated q-int))
(define q-bool (q-satisfy qtest-bool 'bool))
(define qa-bool (p-annotated q-bool))
(define (q-lit lit)
  (let ((r (q-satisfy (qtest-lit lit) 'lit)))
    (set! r.label (sexp (sym 'lit) lit))
    r))
(define (qa-lit lit) (p-annotated (q-lit lit)))
(define (q-litsym s) (q-lit (sexp:symbol s)))
(define (qa-litsym s) (p-annotated (q-litsym s)))
(define q-sym (q-satisfy qtest-sym 'sym))
(define qa-sym (p-annotated q-sym))
(define q-wild (q-satisfy qtest-wild 'wild))
(define qa-wild (p-annotated q-wild))

;; ----- list of parsers -----

(define p-seq*
  ()        -> (returnP (list:nil) (sexp:symbol 'nil))
  (hd . tl) -> (consP hd (p-seq* tl))
  )

(define (zp-list0 parsers)
  (zp-list* (wrap-label 'list parsers) (p-seq* parsers)))

(define (zp-list* label seq)
  (define inner
    ()
    -> (result:no null-src label "empty list")
    ((sexp:list subs) . rest)
    -> (match (seq.fun subs) with
         (result:ok src v ())
         -> (result:ok src (zparse:list v) rest)
         (result:ok src v (hd . tl))
         -> (let (((src0 _) (sexp->src hd)))
              (result:fail src0 label "unexpected item"))
         (result:no src lab err)
         -> (result:no src lab err)
         (result:fail src lab err)
         -> (result:fail src lab err)
         )
    (_ . rest)
    -> (result:no null-src label "expected list")
    )
  (parser/make inner label)
  )

(defmacro zp-list
  (zp-list p ...) -> (zp-list0 (list p ...))
  )

(defmacro za-list
  (za-list p ...) -> (p-annotated (zp-list p ...))
  )

(define (p-form* sym parsers)
  (zp-list*
   (wrap-label sym parsers)
   (consP (qa-litsym sym)
          (must (p-seq* parsers))
          )))

(define (mp-form* sym fun parsers)
  (mapP fun (p-form* sym parsers) sym))

(defmacro mp-form
  (mp-form sym fun p ...) -> (mp-form* sym fun (list p ...))
  )

(defmacro p-form
  (p-form sym p ...) -> (p-form* sym (list p ...))
  )

(defmacro pa-form
  (pa-form sym p ...) -> (p-annotated (p-form sym p ...))
  )

;; ----- parse-type -----

(define int-type-alist
  (alist/make
   ('i1 i1)
   ('i8 i8)
   ('i16 i16)
   ('i32 i32)
   ('i64 i64)
   ('i128 i128)
   ('i256 i256)
  ))

(define qtest-int-type
  (sexp:symbol s)
  -> (match (alist/lookup int-type-alist s) with
       (maybe:yes t) -> (maybe:yes (zparse:type t))
       (maybe:no) -> (maybe:no)
       )
  _
  -> (maybe:no)
  )

(define qtest-none-type
  (sexp:symbol 'none)
  -> (maybe:yes (zparse:type none))
  _
  -> (maybe:no)
  )

(define q-int-type (q-satisfy qtest-int-type 'int-type))
(define qa-int-type (p-annotated q-int-type))
(define q-none-type (q-satisfy qtest-none-type 'none-type))
(define qa-none-type (p-annotated q-none-type))

(define (imp)
  (raise (:Impossible)))

;; type ::=
;;   i8 i16 .. i256 ;; integers from one to 32 bytes
;;   (VEC int type) ;; fixed-length vector
;;   (REF type)     ;; reference
;;   (QUOTE name)   ;; type variable
;;   (ARROW type type ...) ;; function signature

(define (zp-type)
  (let ((tvars (cmap/make symbol-index-cmp)))

    (define m-vec
      (zparse:list (_ (zparse:int size) (zparse:type sub))) -> (zparse:type (type/vec size sub))
      _ -> (imp)
      )
    (define m-ref
      (zparse:list (_ (zparse:type sub))) -> (zparse:type (type/ref sub))
      _ -> (imp)
      )
    (define m-tvar
      (zparse:list (_ (zparse:sym s))) -> (zparse:type (type/var (cmap/add tvars s)))
      _ -> (imp)
      )

    (define m-arrow
      (zparse:list (_ (zparse:type rtype) (zparse:list argtypes)))
      -> (zparse:type (type/arrow rtype (map zparse->type argtypes)))
      _ -> (imp)
      )

    (fix
     (lambda (zp-type*)
       (p-annotated ;; factored out
        (choice
         q-int-type
         q-none-type
         (mp-form 'vec m-vec qa-int zp-type*)
         (mp-form 'ref m-ref zp-type*)
         (mp-form 'quote m-tvar qa-sym)
         (mp-form '-> m-arrow zp-type* (zp-star zp-type*))
         ))))
    ))

(define zparse->type
  (zparse:type t) -> t
  _ -> (imp)
  )

(define zparse->exp
  (zparse:exp e) -> e
  _ -> (imp)
  )

(define (parse-type exp)
  (let ((p-type (zp-type)))
    (match (p-type.fun (list exp)) with
      (result:ok src type rest)
      -> (:tuple src (zparse->type type))
      (result:fail src label err)
      -> (begin
           (printf (bold "failed to parse type") " while reading " (repr exp) "\n")
           (printf " expected: " (repr label) "\n")
           (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
           (raise (:ParseFail)))
      (result:no src label err)
      -> (begin
           (printf (bold "failed to parse type") " while reading " (repr exp) "\n")
           (printf " expected: " (repr label) "\n")
           (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
           (raise (:ParseFail)))
      )))

;; ----- parse-exp -----

;; note: also used by zp-defn.
;; x:i32 => (%typed x i32)
(define zp-tname
  (map-ann ma-tname (za-list (q-litsym '%typed) q-sym (must (zp-type)))))

(define ma-tname
  src (zparse:list (_ (zparse:sym name) (zparse:type t)))
  -> (zparse:tname (aztname:t name t src))
  src _ -> (imp)
  )

;; probably better done with a macro.
(define m-body
  ((zparse:exp one))
  -> one
  many
  -> (match many with
       ((zparse:exp (azexp:t exp src)) . tl)
       -> (azexp:t (zexp:seq (map zparse->exp many)) src)
       _
       -> (imp)
       )
  _
  -> (imp)
  )

(define (zp-exp)

  (define (m-ann src exp)
    (zparse:exp (azexp:t exp src)))

  (define m-int
    (zparse:int n) -> (zexp:lit (zlit:int n))
    _ -> (imp)
    )
  (define m-var
    (zparse:sym s) -> (zexp:ref s)
    _ -> (imp)
    )
  (define m-begin
    (zparse:list (_ (zparse:list exps)))
    -> (zexp:seq (map zparse->exp exps))
    _ -> (imp)
    )
  (define m-if
    (zparse:list (_ (zparse:exp texp) (zparse:exp cexp) (zparse:exp aexp)))
    -> (zexp:if texp cexp aexp)
    _ -> (imp)
    )
  ;; (define m-set!
  ;;   (zparse:list (_ (zparse:sym name) (zparse:exp val)))
  ;;   -> (zexp:set name val)
  ;;   _ -> (imp)
  ;;   )
  (define m-appk
    (zparse:list (_ (zparse:sym name) (zparse:list args)))
    -> (zexp:appk name (map zparse->exp args))
    _ -> (imp)
    )
  (define m-call
    (zparse:list ((zparse:sym name) (zparse:list args)))
    -> (zexp:call name (map zparse->exp args))
    _ -> (imp)
    )
  (define m-prim
    (zparse:list (_ (zparse:sym name) (zparse:wild param) (zparse:list args)))
    ;;-> (zexp:prim name (remove-annotations param) (map zparse->exp args))
    -> (zexp:prim name param (map zparse->exp args))
    _ -> (imp)
    )

  (define m-let
    (zparse:list (_ (zparse:opt mloop) (zparse:list ((zparse:list binds))) (zparse:list exps)))
    -> (m-let0 mloop binds exps)
    _ -> (imp)
    )

  (define m-let0
    (maybe:yes (zparse:sym name)) binds exps
    -> (zexp:loop name (map m-bind binds) (m-body exps))
    (maybe:no) binds exps
    -> (m-let1 (m-body exps) (reverse binds))
    _ _ _
    -> (imp)
    )

  (define m-let1
    body ()
    -> (azexp/exp body)
    body ((zparse:list ((zparse:tname tname) (zparse:exp init))) . binds)
    -> (m-let1 (azexp:t (zexp:let tname init body) (aztname/src tname)) binds)
    _ _
    -> (imp)
    )

  (define m-bind
    (zparse:list ((zparse:tname tname) (zparse:exp init)))
    -> (:tuple tname init)
    _
    -> (imp)
    )

  ;; exp ::=
  ;;   lit
  ;;   (BEGIN exp ...)
  ;;   (SET! name exp)
  ;;   (IF exp exp exp)
  ;;   (LET ((name exp) ...) exp ...)
  ;;   (LET name ((name exp) ...) exp ...)
  ;;   (APPK name exp ...)
  ;;   (PRIM name sexp exp ...)
  ;;   (name exp ...)

  (fix
   (lambda (zp-exp*)
     (map-ann
      m-ann
      (p-annotated
       (choice
        (mapP m-int q-int 'm-int) ;; literal
        (mapP m-var q-sym 'm-var) ;; varref
        (mp-form 'begin m-begin (zp-plus zp-exp*))
        (mp-form 'if m-if zp-exp* zp-exp* zp-exp*)
        ;; note: linearization of let could/should be done by a macro.
        (mp-form 'let m-let
                 (zp-opt qa-sym)
                 (za-list (zp-star (za-list zp-tname zp-exp*)))
                 (zp-plus zp-exp*))
        ;; (mp-form 'set! m-set! qa-sym zp-exp*)
        (mp-form 'appk m-appk qa-sym (zp-star zp-exp*))
        (mp-form 'prim m-prim qa-sym qa-wild (zp-star zp-exp*))
        (mapP m-call (zp-list qa-sym (zp-star zp-exp*)) 'm-app)
        ))))))

;; ----- definitions -----
;; def ::=
;;   (DEFINE (name formal ...) exp ...)
;; def ::=
;;   (DEFINE name:type exp)

(define m-tname
  (zparse:tname tname)
  -> tname
  _
  -> (imp)
  )

(define m-defn
  (zparse:list (_ (zparse:list ((zparse:list (name . formals)))) (zparse:list exps)))
  -> (ztop:fun (m-tname name) (map m-tname formals) (m-body exps))
  _
  -> (imp)
  )

(define (zp-defn)
  (p-annotated (mp-form 'define m-defn (za-list (zp-plus zp-tname)) (zp-plus (zp-exp))))
  )

(define sexp->zlit
  (sexp:int n)       -> (zlit:int n)
  (sexp:vector subs) -> (zlit:vec (map sexp->zlit subs))
  other              -> (raise (:ParseFail))
  )

;; XXX or map-ann & create azlit
(define m-defl
  (zparse:list (_ (zparse:tname tname) (zparse:wild val)))
  -> (ztop:lit tname (sexp->zlit (remove-annotations val)))
  _
  -> (imp)
  )

;; XXX bit of a cop-out using qa-wild for vector literals.
(define (zp-defl)
  (p-annotated (mp-form 'deflit m-defl zp-tname qa-wild))
  )

;; ----- declarations -----

(define m-decl
  (zparse:list (_ (zparse:sym name) (zparse:list argtypes) _ (zparse:type rtype)))
  -> (ztop:decl name (type/arrow rtype (map zparse->type argtypes)))
  _
  -> (imp)
  )

(define (zp-decl)
  (p-annotated
   (mp-form 'declare m-decl
            qa-sym (zp-star (zp-type)) (qa-litsym '->) (zp-type))))

;; ----- macros -----

(define unwild
  (zparse:wild exp) -> exp
  _ -> (imp)
  )

(define m-macro
  src (zparse:list (_ (zparse:sym name) (zparse:list pairs)))
  -> (ztop:mac name src (macro/parse (map unwild pairs)))
  src _
  -> (imp)
  )

(define (zp-macro)
  (map-ann m-macro (pa-form 'defmacro qa-sym (zp-plus q-wild))))

;; ----- all top-level objects -----

(define (zp-top)
  (choice
   (zp-defn)
   (zp-defl)
   (zp-decl)
   (zp-macro)
   ))
