;; -*- Mode: Irken -*-

;; value types in the user language.
;; for now, no signed types.  we'll add them later if absolutely needed.
;; for now, no algebraic datatypes (or structs).

(datatype vtype      ;; llvm equiv
  (:int int)         ;; i8, i16, ...
  (:array int vtype) ;; [ 2 x i32 ]
  (:ref vtype)       ;; *i64
  )

(define vtype->sexp
  (vtype:int 1)     -> (sexp:symbol 'i1)
  (vtype:int 8)     -> (sexp:symbol 'i8)
  (vtype:int 16)    -> (sexp:symbol 'i16)
  (vtype:int 32)    -> (sexp:symbol 'i32)
  (vtype:int 64)    -> (sexp:symbol 'i64)
  (vtype:int 128)   -> (sexp:symbol 'i128)
  (vtype:int 256)   -> (sexp:symbol 'i256)
  (vtype:int n)     -> (sexp (sym 'int) (int n))
  (vtype:array n t) -> (sexp (sym 'array) (int n) (vtype->sexp t))
  (vtype:ref t)     -> (sexp (sym 'ref) (vtype->sexp t))
  )

(define parse-vtype
  (sexp:symbol 'i1)   -> (vtype:int 1)
  (sexp:symbol 'i8)   -> (vtype:int 8)
  (sexp:symbol 'i16)  -> (vtype:int 16)
  (sexp:symbol 'i32)  -> (vtype:int 32)
  (sexp:symbol 'i64)  -> (vtype:int 64)
  (sexp:symbol 'i128) -> (vtype:int 128)
  (sexp:symbol 'i256) -> (vtype:int 256)
  (sexp:list ((sexp:symbol 'vec) (sexp:int size) type))
  -> (vtype:array size (parse-vtype type))
  (sexp:list ((sexp:symbol 'ref) type))
  -> (vtype:ref (parse-vtype type))
  x -> (raise (:ParseVtypeFailed x))
  )

;; let's use integer tvars, and solve for types using
;;   a simple unifier.

(typealias tvar int)

;; --------------------------------
;; extract types from binding forms
;; --------------------------------

(define (clexp->types exp)
  (let ((map (tree:empty)))

    (define (add name type)
      (tree/insert! map symbol-index-cmp name type))

    (define (add* pairs)
      (for-list pair pairs
        (match pair with
          (:tuple name type)
          -> (add name type))))

    (define (Wbinds binds)
      (for-list bind binds
        (match bind with
          (:tuple (:tuple var type) init)
          -> (begin (add var type) (W init))
          )))

    (define (W* exps)
      (for-list exp exps
        (W exp)))

    (define W
      (clexp:lit n)                -> #u
      (clexp:prim name args)       -> (W* args)
      (clexp:seq exps)             -> (W* exps)
      (clexp:let name t init body) -> (begin (add name t) (W init) (W body))
      (clexp:ref name)             -> #u
      (clexp:set name val)         -> (W val)
      (clexp:if t c a)             -> (begin (W t) (W c) (W a))
      (clexp:call n args)          -> (W* args)
      (clexp:loop n binds b)       -> (begin (Wbinds binds) (W b))
      (clexp:appk n args)          -> (W* args)
      )
    (W exp)
    map
    ))

(define (dump-type-map m)
  (for-map name vtype m
    (printf (lpad 10 (sym name)) " = " (sexp (vtype->sexp vtype)) "\n")
    ))
