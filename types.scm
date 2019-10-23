;; -*- Mode: Irken -*-

;; value types in the user language.
;; for now, no signed types.  we'll add them later if absolutely needed.
;; for now, no algebraic datatypes (or structs).

(require "lib/counter.scm")

(typealias typerec {parent=(maybe type)})

(defmacro typerec/new
  (newtyperec) -> {parent=(maybe:no)}
  )

(datatype type
  (:int int typerec)
  (:vec int type typerec)
  (:arrow type (list type) typerec)
  (:ref type typerec)
  (:var int typerec)
  ;; I think we need this, too.
  ;; (:bool bool typerec)
  )

(define (type/int n)
  (type:int n (typerec/new)))

(define (type/vec n t)
  (type:vec n t (typerec/new)))

(define (type/arrow rtype argtypes)
  (type:arrow rtype argtypes (typerec/new)))

(define (type/ref t)
  (type:ref t (typerec/new)))

(define (type/var i)
  (type:var i (typerec/new)))

(define tvar-counter (make-counter 0))

(define (new-tvar)
  (type/var (tvar-counter.inc)))

(define type->trec
  (type:int _ r)     -> r
  (type:vec _ _ r)   -> r
  (type:arrow _ _ r) -> r
  (type:ref _ r)     -> r
  (type:var _ r)     -> r
  )

(define type<? magic<?)

;; singleton base types
(define i1   (type/int 1))
(define i8   (type/int 8))
(define i16  (type/int 16))
(define i32  (type/int 32))
(define i64  (type/int 64))
(define i128 (type/int 128))
(define i256 (type/int 256))

(define type->sexp
  (type:int 1 _)      -> (sexp:symbol 'i1)
  (type:int 8 _)      -> (sexp:symbol 'i8)
  (type:int 16 _)     -> (sexp:symbol 'i16)
  (type:int 32 _)     -> (sexp:symbol 'i32)
  (type:int 64 _)     -> (sexp:symbol 'i64)
  (type:int 128 _)    -> (sexp:symbol 'i128)
  (type:int 256 _)    -> (sexp:symbol 'i256)
  (type:int n _)      -> (sexp (sym 'int) (int n))
  (type:vec n t _)    -> (sexp (sym 'vec) (int n) (type->sexp t))
  (type:ref t _)      -> (sexp (sym 'ref) (type->sexp t))
  (type:var i _)      -> (sexp (sym 'quote) (sym (string->symbol (format (int i)))))
  (type:arrow r xs _) -> (sexp (sym '->) (type->sexp r) (list (map type->sexp xs)))
  )

(define parse-type
  (sexp:symbol 'i1)   -> i1
  (sexp:symbol 'i8)   -> i8
  (sexp:symbol 'i16)  -> i16
  (sexp:symbol 'i32)  -> i32
  (sexp:symbol 'i64)  -> i64
  (sexp:symbol 'i128) -> i128
  (sexp:symbol 'i256) -> i256
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
  x -> (raise (:ParseTypeFailed x))
  )

;; follow the links to the ultimate parent of this type.
(define (type-find t)
  (let ((trec (type->trec t)))
    (match trec.parent with
      (maybe:no)     -> t
      (maybe:yes t0) -> (let ((p (type-find t0)))
                          (set! trec.parent (maybe:yes p)) ;; path compression
                          p))))

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
      _                _                -> (let ((rb (type->trec pb)))
                                             (set! rb.parent (maybe:yes pa)))
      )))

(define (unify t0 t1)

  (define (type-error t0 t1)
    (let ((t0s (type->sexp t0))
          (t1s (type->sexp t1)))
      (printf "U " (sexp t0s) " != " (sexp t1s) "\n")
      (raise (:TypeError (:Unify t0s t1s)))
      ))

  (define U-int
    ;; allow t0 to unify with any other legit int.
    ;; [i.e. t0 acts like a type variable for integer size]
    (type:int 0 _) (type:int 0 _)   -> (type-error t0 t1)
    (type:int 0 _) (type:int nv _)  -> #u
    (type:int nu _) (type:int 0 _)  -> #u
    (type:int nu _) (type:int nv _) -> (if (= nu nv) #u (type-error t0 t1))
    _ _ -> (raise (:SayWhat?))
    )

  (define (U t0 t1)
    (printf "U " (sexp (type->sexp t0)) " " (sexp (type->sexp t1)) "\n")
    (let ((u (type-find t0))
          (v (type-find t1)))
      (when (not (eq? u v))
        (match u v with
          (type:int nu _) (type:int nv _)
          -> (U-int u v)
          (type:vec nu tu _) (type:vec nv tv _)
          -> (if (= nu nv) (U tu tv) (type-error t0 t1))
          (type:arrow ru argsu _) (type:arrow rv argsv _)
          -> (begin (U ru rv) (for-each2 U argsu argsv))
          (type:ref tu _) (type:ref tv _)
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
        (type:var _ _)        -> t0
        (type:vec n vt r)     -> (type:vec n (p vt) r)
        (type:arrow rt ats r) -> (type:arrow (p rt) (map p ats) r)
        (type:ref rt r)       -> (type:ref (p rt) r)
        (type:int _ _)        -> t0
        )))
  (p t))


;;; ;; literals
;;; 
;;; (datatype literal
;;;   (:int int)               ;; size value
;;;   (:vector (list literal)) ;; elem-type size elements
;;;   )
;;; 
;;; 
;;; ;; let's use integer tvars, and solve for types using
;;; ;;   a simple unifier.
;;; 
;;; (typealias tvar int)
;;; 
;;; ;; --------------------------------
;;; ;; extract types from binding forms
;;; ;; --------------------------------
;;; 
;;; (define (clexp->types exp)
;;;   (let ((map (tree:empty)))
;;; 
;;;     (define (add name type)
;;;       (tree/insert! map symbol-index-cmp name type))
;;; 
;;;     (define (add* pairs)
;;;       (for-list pair pairs
;;;         (match pair with
;;;           (:tuple name type)
;;;           -> (add name type))))
;;; 
;;;     (define (Wbinds binds)
;;;       (for-list bind binds
;;;         (match bind with
;;;           (:tuple (:tuple var type) init)
;;;           -> (begin (add var type) (W init))
;;;           )))
;;; 
;;;     (define (W* exps)
;;;       (for-list exp exps
;;;         (W exp)))
;;; 
;;;     (define W
;;;       (clexp:lit n)                -> #u
;;;       (clexp:prim name args)       -> (W* args)
;;;       (clexp:seq exps)             -> (W* exps)
;;;       (clexp:let name t init body) -> (begin (add name t) (W init) (W body))
;;;       (clexp:ref name)             -> #u
;;;       (clexp:set name val)         -> (W val)
;;;       (clexp:if t c a)             -> (begin (W t) (W c) (W a))
;;;       (clexp:call n args)          -> (W* args)
;;;       (clexp:loop n binds b)       -> (begin (Wbinds binds) (W b))
;;;       (clexp:appk n args)          -> (W* args)
;;;       )
;;;     (W exp)
;;;     map
;;;     ))
;;; 
;;; (define (dump-type-map m)
;;;   (for-map name vtype m
;;;     (printf (lpad 10 (sym name)) " = " (sexp (vtype->sexp vtype)) "\n")
;;;     ))
;;; 
;;; ;; -------------------------
;;; ;; build types for a cps exp
;;; ;; -------------------------
;;; 
;;; (define (type=? ta tb)
;;;   (magic=? ta tb))
;;; 
;;; ;; XXX we need a way to match a vtype with a literal.
;;; ;; for example, if we say (+ 0 1 2 3) we have no way to
;;; ;; know what integer type to attach.  Hrmmmm. I think we need
;;; ;; a H-M style unifier.
;;; 
;;; ;; is this type suitable for arithmetic ops?
;;; (define arith?
;;;   (vtype:int _)                 -> #t
;;;   (vtype:array _ (vtype:int _)) -> #t
;;;   _                             -> #f
;;;   )
;;; 
;;; ;; verify all args are arith and the same. returns that type.
;;; (define prim-arith-sig
;;;   (arg0 . rest)
;;;   -> (if (and (arith? arg0) (every? (lambda (x) (type=? x arg0))))
;;;          (maybe:yes arg0)
;;;          (maybe:no))
;;;   ()
;;;   -> (raise (:Impossible))
;;;   )
;;; 
;;; ;; verify all args are arith and the same.  returns i1.
;;; (define prim-cmp-sig
;;;   (arg0 . rest)
;;;   -> (if (and (arith? arg0) (every? (lambda (x) (type=? x arg0))))
;;;          (maybe:yes (vtype:int 1))
;;;          (maybe:no))
;;;   ()
;;;   -> (raise (:Impossible))
;;;   )
;;; 
;;; (define prim-type-map
;;;   (alist/make
;;;    ('+     prim-arith-sig)
;;;    ('-     prim-arith-sig)
;;;    ('*     prim-arith-sig)
;;;    ('/     prim-arith-sig)
;;;    ('and   prim-arith-sig)
;;;    ('or    prim-arith-sig)
;;;    ('xor   prim-arith-sig)
;;;    ('<<    prim-arith-sig)
;;;    ('>>    prim-arith-sig)
;;;    ('ashr  prim-arith-sig)
;;;    ('=     prim-cmp-sig)
;;;    ('<>    prim-cmp-sig)
;;;    ('<     prim-cmp-sig)
;;;    ('>     prim-cmp-sig)
;;;    ('<=    prim-cmp-sig)
;;;    ('>=    prim-cmp-sig)
;;;    ))
;;; 
;;; (define (build-types varmap exp args)
;;;   (let ((env (tree/empty))            ;; map of var -> type
;;;         (tmap (cmap/make magic-cmp))) ;; map of unique types
;;; 
;;;     (define (lookup-var-type x)
;;;       (match (tree/member env symbol-index-cmp x) with
;;;         (maybe:yes type) -> type
;;;         (maybe:no) -> (raise (:NoTypeForVar x))
;;;         ))
;;; 
;;;     (define (Tprim tv n vars
;;; 
;;; 
;;;     (define T
;;;       (cps:prim tv n x vars k)
;;;       -> (match (alist/lookup prim-type-map n) with
;;;            (maybe:yes check)
;;;            -> (match (check (map lookup-var-type vars)) with
;;;                 (maybe:yes rtype)
;;;                 -> (let ((tv0 (cmap/add tmap rtype)))
;;;                      (cps:prim tv0 n x vars (T k)))
;;;                 (maybe:no)
;;;                 -> (raise (:TypeError tv)))
;;;            (maybe:no)
;;;            -> (raise (:UnknownPrim n))
;;;            )
;;;       (cps:letval tv x v k)
;;;       -> 
