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
  (vtype:int 1) -> (sexp:symbol 'i1)
  (vtype:int 8) -> (sexp:symbol 'i8)
  (vtype:int 16) -> (sexp:symbol 'i16)
  (vtype:int 32) -> (sexp:symbol 'i32)
  (vtype:int 64) -> (sexp:symbol 'i64)
  (vtype:int 128) -> (sexp:symbol 'i128)
  (vtype:int 256) -> (sexp:symbol 'i256)
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

