;; -*- Mode: Irken -*-

;; value types in the user language.
;; for now, no signed types.  we'll add them later if absolutely needed.
;; for now, no algebraic datatypes (or structs).

(require "lib/counter.scm")

(typealias typerec {parent=(maybe type)})

(defmacro typerec/new
  (typerec/new) -> {parent=(maybe:no)}
  )

;; idea: if we can crack this notion of 'kinds', we could
;;  introduce a 'kind' for integer parameters, and a 'kind'
;;  for integer ranges.  then we could represent "iterating
;;  over a range" in a way that safely indexes vectors [by
;;  either knowing that an index is in range or knowing how
;;  to check that range].
;;
;; though: dependent types might obsolete kinds altogether?

(datatype type
  (:none)
  (:int int)
  (:vec int type)
  (:arrow type (list type))
  (:ref type) ;; constant reference
  (:mut type) ;; mutable reference
  (:var int typerec)
  )

(define (type/var i)
  (type:var i (typerec/new)))

(define tvar-counter (make-counter 0))

(define (new-tvar)
  (type/var (tvar-counter.inc)))

(define type<? magic<?)

;; NOTE: all types will be renamed 'uN' rather than 'iN' to reflect
;;  our only-unsigned positioning.

;; singleton base types
(define i0   (type:int 0))
(define i1   (type:int 1))
(define i8   (type:int 8))
(define i16  (type:int 16))
(define i32  (type:int 32))
(define i64  (type:int 64))
(define i128 (type:int 128))
(define i256 (type:int 256))
(define none (type:none))

;; consider: (type:arrow (list type))
;;   so void functions can be represented without hacks.

(define type->sexp
  (type:int 0)      -> (sexp:symbol 'i0)
  (type:int 1)      -> (sexp:symbol 'i1)
  (type:int 8)      -> (sexp:symbol 'i8)
  (type:int 16)     -> (sexp:symbol 'i16)
  (type:int 32)     -> (sexp:symbol 'i32)
  (type:int 64)     -> (sexp:symbol 'i64)
  (type:int 128)    -> (sexp:symbol 'i128)
  (type:int 256)    -> (sexp:symbol 'i256)
  (type:int n)      -> (sexp (sym 'int) (int n))
  (type:vec n t)    -> (sexp (sym 'vec) (int n) (type->sexp t))
  (type:ref t)      -> (sexp (sym 'ref) (type->sexp t))
  (type:mut t)      -> (sexp (sym 'mut) (type->sexp t))
  (type:var i _)    -> (sexp (sym 'quote) (sym (string->symbol (format (int i)))))
  (type:arrow r xs) -> (sexp (sym '->) (type->sexp r) (list (map type->sexp xs)))
  (type:none)       -> (sexp:symbol 'none)
  )

(define (type-repr t)
  (repr (type->sexp t)))

(define parse-size
  (sexp:int size)
  -> size
  (sexp:list ((sexp:symbol '%int) (sexp:int 10) (sexp:string digits)))
  -> (string->int digits)
  exp
  -> (raise (:ParseTypeFailed exp))
  )

(define parse-type
  (sexp:symbol 'i0)   -> i0
  (sexp:symbol 'i1)   -> i1
  (sexp:symbol 'i8)   -> i8
  (sexp:symbol 'i16)  -> i16
  (sexp:symbol 'i32)  -> i32
  (sexp:symbol 'i64)  -> i64
  (sexp:symbol 'i128) -> i128
  (sexp:symbol 'i256) -> i256
  (sexp:symbol 'none) -> none
  ;; vector
  (sexp:list ((sexp:symbol 'vec) size type))
  -> (type:vec (parse-size size) (parse-type type))
  ;; reference
  (sexp:list ((sexp:symbol 'ref) type))
  -> (type:ref (parse-type type))
  ;; mutable reference
  (sexp:list ((sexp:symbol 'mut) type))
  -> (type:mut (parse-type type))
  ;; type variable
  (sexp:list ((sexp:symbol 'quote) (sexp:int i)))
  -> (type/var i)
  (sexp:list ((sexp:symbol 'arrow) rtype (sexp:list argtypes)))
  -> (type:arrow (parse-type rtype) (map parse-type argtypes))
  (sexp:list ((sexp:symbol '->) rtype (sexp:list argtypes)))
  -> (type:arrow (parse-type rtype) (map parse-type argtypes))
  x -> (raise (:ParseTypeFailed x))
  )

