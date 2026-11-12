;; -*- Mode: Irken -*-

;; value types in the user language.
;; for now, no signed types.  we'll add them later if absolutely needed.
;; for now, no algebraic datatypes (or structs).

(require "lib/counter.scm")

;; idea: if we can crack this notion of 'kinds', we could
;;  introduce a 'kind' for integer parameters, and a 'kind'
;;  for integer ranges.  then we could represent "iterating
;;  over a range" in a way that safely indexes vectors [by
;;  either knowing that an index is in range or knowing how
;;  to check that range].
;;
;; though: dependent types might obsolete kinds altogether?

(datatype tvar
  (:t int {parent=(maybe 'a)})
  )

;; almost thinking we might want *two* integer kinds,
;;  one for 'width', and another for 'size', since these
;;  are different uses. [would a 'range' kind be another?]
(datatype itype
  (:fix int)
  (:var (tvar itype))
  (:dyn symbol)
  )

;; note: vector? is a 'boolean itype'.  in other words, it's an
;;  'itype' that is used as a boolean (0, 1, or ?).  The alternative
;;  is to provide yet another 'kind', and needlessly complicate
;;  type-find, type-union, etc.
;;
;; its purpose is to identify when vectors are used in vector-like
;;  ways [versus pointer-to-array ways] so we don't have to push that
;;  llvm distinction all the way up into the gaz language.

(datatype type
  (:none)
  (:int itype)              ;; integer, size
  (:vec itype itype type)   ; vector?, size, type.
  (:arrow type (list type)) ;; rtype, argtypes
  (:ref type)               ;; constant reference
  (:mut type)               ;; mutable reference
  (:var (tvar type))        ;; type variable.
  )

;; itype used as a boolean
(define btype-repr
  (itype:fix 0) -> "#F"
  (itype:fix _) -> "#T"
  (itype:var _) -> "?"
  (itype:dyn _) -> "!" ;; malformed
  )

(define btype-true  (itype:fix 1))
(define btype-false (itype:fix 0))

(define type-repr
  (type:none)                              -> "none"
  (type:int (itype:fix n))                 -> (format "i" (int n))
  (type:int (itype:var (tvar:t n _)))      -> (format "(int '" (int n) ")")
  (type:int (itype:dyn name))              -> (format "(int " (ansi red (sym name)) ")") ;; malformed
  (type:vec v? (itype:fix n) t)            -> (format "(vec " (btype-repr v?) " " (int n) " " (type-repr t) ")")
  (type:vec v? (itype:var (tvar:t n _)) t) -> (format "(vec " (btype-repr v?) " '" (int n) " " (type-repr t) ")")
  (type:vec v? (itype:dyn name) t)         -> (format "(vec " (btype-repr v?) " " (ansi yellow (sym name)) " " (type-repr t) ")")
  (type:arrow rt txs)                      -> (format "(" (join type-repr " " txs) " -> " (type-repr rt) ")")
  (type:ref t)                             -> (format "(ref " (type-repr t) ")")
  (type:mut t)                             -> (format "(mut " (type-repr t) ")")
  (type:var (tvar:t n _))                  -> (format "'" (int n))
  )

(define (type/var i)
  (type:var (tvar:t i {parent=(maybe:no)})))

(define (itype/var i)
  (itype:var (tvar:t i {parent=(maybe:no)})))

(define tvar-counter (make-counter 0))

(define (new-tvar)
  (type/var (tvar-counter.inc)))

(define (new-itvar)
  (itype/var (tvar-counter.inc)))

;; NOTE: all types will be renamed 'uN' rather than 'iN' to reflect
;;  our only-unsigned positioning.

;; singleton base types
(define i1   (type:int (itype:fix 1)))
(define i8   (type:int (itype:fix 8)))
(define i16  (type:int (itype:fix 16)))
(define i31  (type:int (itype:fix 31)))
(define i32  (type:int (itype:fix 32)))
(define i64  (type:int (itype:fix 64)))
(define i128 (type:int (itype:fix 128)))
(define i256 (type:int (itype:fix 256)))
(define none (type:none))

;; consider: (type:arrow (list type))
;;   so void functions can be represented without hacks.

(define tvar->sexp
  (tvar:t i _) -> (sexp (sym 'quote) (sym (string->symbol (format (int i)))))
  )

(define itype->sexp
  (itype:fix n)    -> (sexp:symbol (string->symbol (format "i" (int n))))
  (itype:var tv)   -> (tvar->sexp tv)
  (itype:dyn name) -> (sexp:symbol name)
  )

(define size->sexp
  (itype:fix n)    -> (sexp:int n)
  (itype:var tv)   -> (tvar->sexp tv)
  (itype:dyn name) -> (sexp:symbol name)
  )

(define type->sexp
  (type:int (itype:fix n)) -> (sexp:symbol (string->symbol (format "i" (int n))))
  (type:int it)     -> (sexp (sym 'int) (itype->sexp it))
  (type:vec v? s t) -> (sexp (sym 'vec) (itype->sexp v?) (size->sexp s) (type->sexp t))
  (type:ref t)      -> (sexp (sym 'ref) (type->sexp t))
  (type:mut t)      -> (sexp (sym 'mut) (type->sexp t))
  (type:var tv)     -> (tvar->sexp tv)
  (type:arrow r xs) -> (sexp (sym '->) (type->sexp r) (list (map type->sexp xs)))
  (type:none)       -> (sexp:symbol 'none)
  )

(define (parse-type sexp)

  (let ((tvarmap (cmap/make symbol-index-cmp)))

    (define parse-size
      (sexp:int size)
      -> (itype:fix size)
      (sexp:list ((sexp:symbol '%int) (sexp:int 10) (sexp:string digits)))
      -> (itype:fix (string->int digits))
      (sexp:list ((sexp:symbol 'quote) (sexp:symbol x)))
      -> (itype/var (cmap/add tvarmap x))
      (sexp:symbol name)
      -> (itype:dyn name)
      exp
      -> (raise (:ParseTypeFailed exp))
      )

    (define P
      (sexp:list ((sexp:symbol 'vec) size type))              -> (type:vec (new-itvar) (parse-size size) (P type))
      (sexp:list ((sexp:symbol 'ref) type))                   -> (type:ref (P type))
      (sexp:list ((sexp:symbol 'mut) type))                   -> (type:mut (P type))
      (sexp:list ((sexp:symbol 'arrow) rtype (sexp:list ts))) -> (type:arrow (P rtype) (map P ts))
      (sexp:list ((sexp:symbol '->) rtype (sexp:list ts)))    -> (type:arrow (P rtype) (map P ts))
      (sexp:list ((sexp:symbol 'quote) (sexp:symbol x)))      -> (type/var (cmap/add tvarmap x))
      (sexp:symbol 'i1)   -> i1
      (sexp:symbol 'i8)   -> i8
      (sexp:symbol 'i16)  -> i16
      (sexp:symbol 'i31)  -> i31
      (sexp:symbol 'i32)  -> i32
      (sexp:symbol 'i64)  -> i64
      (sexp:symbol 'i128) -> i128
      (sexp:symbol 'i256) -> i256
      (sexp:symbol 'none) -> none
      x                   -> (raise (:ParseTypeFailed x))
      )
    (instantiate-type (P sexp))
    )
  )

;; replace all type variables (of both kinds) with
;;  fresh ones. this is too complicated.

(define (instantiate-type t)
  (let ((tvm (tree/empty))
        (itvm (tree/empty)))

    (define (Wi itype)
      (match itype with
        (itype:fix n) -> itype
        (itype:dyn name) -> itype
        (itype:var (tvar:t i r))
        -> (match (tree/member itvm int-cmp i) with
             (maybe:yes itv) -> itv
             (maybe:no)
             -> (let ((itv (new-itvar)))
                  (tree/insert! itvm int-cmp i itv)
                  itv))))

    (define (W t)
      (match t with
        (type:none)             -> t
        (type:int itype)        -> (type:int (Wi itype))
        (type:vec v? size base) -> (type:vec v? (Wi size) (W base)) ;; note: bool-itvar
        (type:arrow rt argts)   -> (type:arrow (W rt) (map W argts))
        (type:ref t)            -> (type:ref (W t))
        (type:mut t)            -> (type:mut (W t))
        (type:var (tvar:t i r))
        -> (match (tree/member tvm int-cmp i) with
             (maybe:yes tv) -> tv
             (maybe:no)
             -> (let ((tv (new-tvar)))
                  (tree/insert! tvm int-cmp i tv)
                  tv))))
    (W t)))

(define type-isvar?
  (type:var tv) -> (maybe:yes tv)
  _ -> (maybe:no)
  )

(define itype-isvar?
  (itype:var tv) -> (maybe:yes tv)
  _ -> (maybe:no)
  )

;; type-find & type-union are quasi-polymorphic in that
;;  they will work on either a `type` or an `itype` depending
;;  on the maybe-predicate passed to them.

;; follow the links to the ultimate parent of this type.
(define (type-find isvar? t)
  (define (R t)
    (match (isvar? t) with
      (maybe:yes (tvar:t n r))
      -> (match r.parent with
           (maybe:no)
           -> t
           (maybe:yes t0)
           -> (let ((p (R t0))) ;; path compression
                (set! r.parent (maybe:yes p))
                p)
           )
      _ -> t
      ))
  (R t)
  )

(define (unify env t0 t1)

  (define (type-error t0 t1)
    (let ((t0s (type->sexp (apply-subst t0)))
          (t1s (type->sexp (apply-subst t1))))
      (printf "U " (sexp t0s) " != " (sexp t1s) "\n")
      (raise (:TypeError (:Unify t0s t1s)))
      ))

  ;; link through type variable
  (define (type-union isvar? a b)
    (match (isvar? a) (isvar? b) with
      (maybe:yes (tvar:t na ra)) (maybe:yes (tvar:t nb rb))
      -> (if (< na nb) ;; gravitate toward smaller index
             (set! rb.parent (maybe:yes a))
             (set! ra.parent (maybe:yes b)))
      (maybe:yes (tvar:t na ra)) (maybe:no)
      -> (set! ra.parent (maybe:yes b))
      (maybe:no) (maybe:yes (tvar:t nb rb))
      -> (set! rb.parent (maybe:yes a))
      (maybe:no) (maybe:no)
      -> #u
      ))

  (define (U-itype it0 it1)
    ;; (printf "U-itype  " (sexp (itype->sexp it0)) " " (sexp (itype->sexp it1)) "\n")
    (let ((u (type-find itype-isvar? it0))
          (v (type-find itype-isvar? it1)))
      (when (not (eq? u v))
        (match u v with
          (itype:fix na) (itype:fix nb) -> (if (= na nb) #u (type-error t0 t1))
          (itype:dyn na) (itype:dyn nb) -> (if (eq? na nb) #u (type-error t0 t1))
          (itype:var _) _ -> (type-union itype-isvar? u v)
          _ (itype:var _) -> (type-union itype-isvar? u v)
          _ _             -> (type-error t0 t1)
          )
        )))

  (define (U t0 t1)
    (printf "U  " (sexp (type->sexp t0)) " " (sexp (type->sexp t1)) "\n")
    (let ((u (type-find type-isvar? t0))
          (v (type-find type-isvar? t1)))
      (printf "U* " (type-repr u) " " (type-repr v) "\n")
      (when (not (eq? u v))
        (match u v with
          (type:none) (type:none)
          -> #u
          (type:int nu) (type:int nv)
          -> (U-itype nu nv)
          (type:vec v0? nu tu) (type:vec v1? nv tv)
          -> (begin (U-itype v0? v1?) (U-itype nu nv) (U tu tv))
          (type:arrow ru argsu) (type:arrow rv argsv)
          -> (begin (U ru rv) (for-each2 U argsu argsv))
          (type:ref tu) (type:ref tv)
          -> (U tu tv)
          (type:mut tu) (type:mut tv)
          -> (U tu tv)
          (type:var _) _ -> (type-union type-isvar? u v)
          _ (type:var _) -> (type-union type-isvar? u v)
          _ _            -> (type-error t0 t1)
          )
        )))

  (U t0 t1)
  )

;; this has the unfortunate effect of copying all type objects,
;;  with no sharing at all.  It might be nice to make a smarter
;;  system that shares type objects when possible.
(define (apply-subst t)

  (define (pi t)
    (type-find itype-isvar? t))

  (define (p t)
    (let ((t0 (type-find type-isvar? t)))
      (match t0 with
        (type:int n)        -> (type:int (pi n))
        (type:vec v? n vt)  -> (type:vec (pi v?) (pi n) (p vt))
        (type:arrow rt ats) -> (type:arrow (p rt) (map p ats))
        (type:ref rt)       -> (type:ref (p rt))
        (type:mut rt)       -> (type:mut (p rt))
        _                   -> t0
        )))
  (p t))
