;; -*- Mode: Irken -*-

;; value types in the user language.
;; for now, no signed types.  we'll add them later if absolutely needed.
;; for now, no algebraic datatypes (or structs).

(require "lib/counter.scm")

(typealias typerec {parent=(maybe type)})

(defmacro typerec/new
  (typerec/new) -> {parent=(maybe:no)}
  )

(datatype type
  (:none)
  (:int int)
  (:vec int type)
  (:arrow type (list type))
  (:ref type)
  (:var int typerec)
  )

(define (type/int n)
  (type:int n))

(define (type/vec n t)
  (type:vec n t))

(define (type/arrow rtype argtypes)
  (type:arrow rtype argtypes))

(define (type/ref t)
  (type:ref t))

(define (type/var i)
  (type:var i (typerec/new)))

(define (type/none)
  (type:none))

(define tvar-counter (make-counter 0))

(define (new-tvar)
  (type/var (tvar-counter.inc)))

(define type<? magic<?)

;; NOTE: all types will be renamed 'uN' rather than 'iN' to reflect
;;  our only-unsigned positioning.

;; singleton base types
(define i0   (type/int 0))
(define i1   (type/int 1))
(define i8   (type/int 8))
(define i16  (type/int 16))
(define i32  (type/int 32))
(define i64  (type/int 64))
(define i128 (type/int 128))
(define i256 (type/int 256))
(define none (type/none))

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
  (sexp:list ((sexp:symbol 'vec) (sexp:int size) type))
  -> (type/vec size (parse-type type))
  ;; reference
  (sexp:list ((sexp:symbol 'ref) type))
  -> (type/ref (parse-type type))
  ;; type variable
  (sexp:list ((sexp:symbol 'quote) (sexp:int i)))
  -> (type/var i)
  (sexp:list ((sexp:symbol 'arrow) rtype (sexp:list argtypes)))
  -> (type/arrow (parse-type rtype) (map parse-type argtypes))
  (sexp:list ((sexp:symbol '->) rtype (sexp:list argtypes)))
  -> (type/arrow (parse-type rtype) (map parse-type argtypes))
  x -> (raise (:ParseTypeFailed x))
  )

;; follow the links to the ultimate parent of this type.
(define (type-find t)
  (match t with
    (type:var n r)
    -> (match r.parent with
         (maybe:no)
         -> t
         (maybe:yes t0)
         -> (let ((p (type-find t0)))
              (set! r.parent (maybe:yes p))
              p)
         )
    t -> t
    ))

;; link through type variable
(define (type-union a b)
  (let ((pa (type-find a))
        (pb (type-find b)))
    (match pa pb with
      (type:var na ra) (type:var nb rb) -> (if (< na nb)
					       (set! rb.parent (maybe:yes pa))
					       (set! ra.parent (maybe:yes pb)))
      (type:var _ ra)  _                -> (set! ra.parent (maybe:yes pb))
      _                (type:var _ rb)  -> (set! rb.parent (maybe:yes pa))
      _ _ -> #u
      )))

(define (unify t0 t1)

  (define (type-error t0 t1)
    (let ((t0s (type->sexp t0))
          (t1s (type->sexp t1)))
      (printf "U " (sexp t0s) " != " (sexp t1s) "\n")
      (raise (:TypeError (:Unify t0s t1s)))
      ))

  ;; XXX I don't think we need this feature.
  ;; YYY now I think we do. (see `vref`).
  ;; ZZZ I think we want dependent types. maybe.
  (define U-int
    ;; allow t0 to unify with any other legit int.
    ;; [i.e. i0 acts like a type variable for integer size]
    (type:int 0) (type:int 0)   -> (type-error t0 t1)
    (type:int 0) (type:int nv)  -> #u
    (type:int nu) (type:int 0)  -> #u
    (type:int nu) (type:int nv) -> (if (= nu nv) #u (type-error t0 t1))
    _ _ -> (raise (:SayWhat?))
    )

  (define (U t0 t1)
    ;; (printf "U " (sexp (type->sexp t0)) " " (sexp (type->sexp t1)) "\n")
    (let ((u (type-find t0))
          (v (type-find t1)))
      (when (not (eq? u v))
        (match u v with
          (type:none) (type:none)
          -> #u
          (type:int nu) (type:int nv)
          -> (U-int u v)
          (type:vec nu tu) (type:vec nv tv)
          -> (if (= nu nv) (U tu tv) (type-error t0 t1))
          (type:arrow ru argsu) (type:arrow rv argsv)
          -> (begin (U ru rv) (for-each2 U argsu argsv))
          (type:ref tu) (type:ref tv)
          -> (U tu tv)
          (type:var _ _) _ -> #u
          _ (type:var _ _) -> #u
          _ _              -> (type-error t0 t1)
          )
        (type-union u v)
        )))

  (U t0 t1)
  )

(define (apply-subst t)
  (define (p t)
    (let ((t0 (type-find t)))
      (match t0 with
        (type:vec n vt)     -> (type:vec n (p vt))
        (type:arrow rt ats) -> (type:arrow (p rt) (map p ats))
        (type:ref rt)       -> (type:ref (p rt))
        _                   -> t0
        )))
  (p t))

