;; -*- mode: gaz -*-

;; this is the beginnings of a 'derived expressions' basis
;;  for gaz.  so all the predefined forms will go in here.
;;
;; some fun crypto-related things that might go in here:
;;
;; * explicit for-range loops.
;; * the same, but with unrolling metadata.
;;
;; top-level expressions are:
;; (%deflit name:type literal)
;; (%define name:type (arg0:type ...) body)
;; (%declare name type)
;; (defmacro ...)

;; core expressions are:
;;
;; (%begin exp ...)
;; (%let-val name:type init body)
;; (%let-loop name ((name:type init) ...) body)
;; (%set! name exp)
;; (%if exp exp exp)
;; (%appk name exp ...)
;; (%prim name param exp ...)
;; (exp exp ...)

(defmacro begin
  (begin one)   -> one
  (begin a ...) -> (%begin a ...)
  )

(defmacro appk
  (appk k) -> (%appk k)
  (appk k a ...) -> (%appk k a ...)
  )

(defmacro declare
  (declare name type) -> (%declare name type)
  )

(defmacro define-constant
  (define-constant (<%typed> name type) litval)
  -> (%deflit (%typed name (ref type)) litval)
  )
(defmacro define-mutable
  (define-mutable (<%typed> name type) litval)
  -> (%deflit (%typed name (mut type)) litval)
  )

(defmacro define
  (define (name) body ...)
  -> (%define name () (begin body ...))
  (define (name arg ...) body ...)
  -> (%define name (arg ...) (begin body ...))
  )

(defmacro let
  (let () body ...)
  -> (begin body ...)
  (let (((<%typed> name type) init)) body ...)
  -> (%let-val (<%typed> name type) init (begin body ...))
  (let (((<%typed> name type) init) binds ...) body ...)
  -> (%let-val (<%typed> name type) init (let (binds ...) body ...))
  (let name (bind ...) body ...)
  -> (%let-loop name (bind ...) (begin body ...))
  )

(defmacro if
  (if tst con alt) -> (%if tst con alt)
  (if tst con)     -> (%if tst con 0)
  )

(defmacro when
  (when test body ...) -> (if test (begin body ...))
  )

(defmacro and
  (and)                 -> 1
  (and test)            -> test
  (and test1 test2 ...) -> (if test1 (and test2 ...) 0)
  )

(defmacro or
  (or)			-> 0
  (or test)		-> test
  (or test1 test2 ...)	-> (if test1 1 (or test2 ...))
  )

(defmacro +
  (+ x)       -> x
  (+ a b ...) -> (%prim + #f a (+ b ...))
  )

(defmacro -
  (- a)         -> (%prim - #f 0 a)
  (- a b)	-> (%prim - #f a b)
  (- a b c ...) -> (- (%prim - #f a b) c ...)
  )

(defmacro *
  (* x)       -> x
  (* a b ...) -> (%prim * #f a (* b ...))
  )

(defmacro =
  (= a b)     -> (%prim = #f a b)
  (= a b ...) -> (and (= a b) (= b ...))
  )

;; consider C names + scheme names?
;; ~, &, |, ^, ...
;; note: scheme seems to have settled (SRFIs 33, 60, 151, 142...?) on
;; bitwise-and, bitwise-xor, etc.

(defmacro xor
  (xor x)       -> x
  (xor a b ...) -> (%prim xor #f a (xor b ...))
  )

(defmacro &
  (& x)       -> x
  (& a b ...) -> (%prim and #f a (& b ...))
  )

(defmacro ior
  (ior a)       -> a
  (ior a b ...) -> (%prim or #f a (ior b ...))
  )

(defmacro ~
  (~ x)       -> (xor (- 1) x)
  )

(defmacro >>>
  (>>> n s)   -> (%prim >>> #f n s)
  )

(defmacro <<<
  (<<< n s)   -> (%prim <<< #f n s)
  )

(defmacro cond
  (cond (<else> e1 ...))
  -> (begin e1 ...)
  (cond (test e1 ...))
  -> (if test (begin e1 ...))
  (cond (test e1 ...)
	c1 ...)
  -> (if test
	 (begin e1 ...)
	 (cond c1 ...)))

(defmacro while
  (while test body ...)
  -> (let $loop ()
       (when test
	 body ...
         (appk $loop)))
  )

(defmacro for-range*
  (for-range* (<%typed> vname vtype) lo hi body ...)
  -> (let $loop (((%typed vname vtype) lo)
                 ((%typed $stop vtype) hi))
       (when (< vname $stop)
         body ...
         (appk $loop (+ vname 1) $stop))))

(defmacro for-range
  (for-range vname num body ...)
  -> (for-range* vname 0 num body ...)
  )

(defmacro %array-ref
  (%array-ref param src index)
  -> (%get (%prim %vref param src index))
  )

;; note: this detects setting an array 'lval', derailing the above `%get`.
(defmacro set!
  (set! (<%array-ref> param src index) val) -> (%set! (%prim %vref param src index) val)
  (set! loc val)                            -> (%set! loc val)
  )

(defmacro inc!
  (inc! n)   -> (set! n (+ n 1))
  (inc! n m) -> (set! n (+ n m))
  )

;; note: type is a sexp param.
(defmacro alloca
  (alloca type) -> (%prim alloca type)
  )

(defmacro letcont
  (letcont (name (var ...) body0 ...) body1 ...)
  -> (%let-cont
      name (var ...)
      (begin body0 ...)
      (begin body1 ...)
      ))
