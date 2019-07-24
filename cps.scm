;; -*- Mode: Irken -*-

;; TODO
;; * consider making clexp:let n-ary rather than devolving it into let*.
;; * add types
;;   we need to extend the universe of values.
;;   previously we had `cons` & `int`.  for crypto we want
;;     the T=i<n>|<vector T> typeset.  we also probably need
;;     a separate `ref` type.  But what can it contain?
;;    [or yet, like in smlnj is a ref type equiv to a length-one vector?]
;;   ok, I've added typed variable bindings (in define, let, and let-loop).
;;   the next step is to infer/propagate all types.
;;
;; * convert var/cvar to int
;;   (this turned out to be a Bad Idea - rewrite all hosed because no distinction)
;;   might want to explore this again later using a real datatype for the various
;;   var types.
;; * add functions (maybe?)
;;   Thought I needed functions for loops, but if instead I expose 'appk' to the user
;;     we can implement loops/recursion directly with conts.  I think.

(typealias var symbol)
(typealias cvar symbol)

;; this will become vtype, and we'll probably have to have a way of defining
;;  literals.
(typealias val int)

;; now, how do we add types?  in irken we added types to the node
;;  record, but I don't think we want that here. we either want:
;; 1) add a type field to every record
;;   pro: straightforward
;;   con: tedious
;;   con: no way to have a partially typed expression.
;;      [unless we either create an 'unknown' type or type during cps conversion]
;;   1a) make the type slot mutable?
;; 2) wrap `cps` with a `tcps` tuple that includes a type.
;;   pro: perhaps simpler?
;;   con: may hurt embedded pattern matches.
;;   con: breaks the datatype recursion.

;; I'm leaning toward 1), with typing during cps conversion.
;; in fact, the more I think about it, using tvars etc is probably
;; the way to go, even if we're not doing full type inference (yet).

(datatype cps
  (:prim tvar symbol var (list var) cps)  ;; x + y
  (:letval tvar var val cps)              ;; letval x = V in L
  (:letcont tvar cvar (list var) cps cps) ;; letcont k x0 x1 ... = K in L
  (:appk tvar cvar (list var))            ;; k x0 x1 ...
  (:app tvar symbol cvar (list var))      ;; f k x0 x1 ...
  (:if tvar var cvar cvar)                ;; if x k1 k2
  (:dead tvar cps)                        ;; K (for seq)
  )

;; note: ignores tvar.
(define cps->sexp
  (cps:prim t n x vars k)    -> (sexp (sym 'prim) (sym n) (sym x)
                                      (list (map sexp:symbol vars))
                                      (cps->sexp k))
  (cps:letval t x v k)       -> (sexp (sym 'letval) (sym x) (int v) (cps->sexp k))
  (cps:letcont t k xs t0 t1) -> (sexp (sym 'letcont) (sym k)
                                      (list (map sexp:symbol xs))
                                      (cps->sexp t0) (cps->sexp t1))
  (cps:appk t k xs)          -> (sexp (sym 'appk) (sym k)
                                      (list (map sexp:symbol xs)))
  (cps:app t n k vars)       -> (sexp (sym 'app) (sym n) (sym k)
                                      (list (map sexp:symbol vars)))
  (cps:if t tst c a)         -> (sexp (sym 'if) (sym tst) (sym c) (sym a))
  (cps:dead t k)             -> (sexp (sym 'dead) (cps->sexp k))
  )

(define prims (list '+ '- '* '/ 'and 'or 'xor '<< '>> 'ashr '= '<> '< '> '<= '>=))

;; --------------
;; CPS conversion
;; --------------

(define (clexp->cps exp)

  (define make-tvar
    (let ((counter 0))
      (lambda ()
        (inc! counter)
        counter)))

  (define (gensym prefix)
    (let ((counter 0))
      (lambda ()
        (inc! counter)
        (string->symbol (format prefix (int counter))))))

  (define genvar (gensym "x"))
  (define gencont (gensym "L"))

  ;; constructors that add a new tvar to every cps.
  (define (cps-prim n x vars k)    (cps:prim (make-tvar) n x vars k))
  (define (cps-letval x v k)       (cps:letval (make-tvar) x v k))
  (define (cps-letcont k xs t0 t1) (cps:letcont (make-tvar) k xs t0 t1))
  (define (cps-appk k xs)          (cps:appk (make-tvar) k xs))
  (define (cps-app n k vars)       (cps:app (make-tvar) n k vars))
  (define (cps-if tst con ant)     (cps:if (make-tvar) tst con ant))
  (define (cps-dead k)             (cps:dead (make-tvar) k))


  (define (cps-args args vars K)
    (match args with
      ()        -> (K (reverse vars))
      (hd . tl) -> (cps hd (lambda (v) (cps-args tl (list:cons v vars) K)))
      ))

  (define (zip items)
    (define loop
      acc0 acc1 ()                    -> (:tuple (reverse acc0) (reverse acc1))
      acc0 acc1 ((:tuple a b) . rest) -> (loop (list:cons a acc0) (list:cons b acc1) rest)
      )
    (loop (list:nil) (list:nil) items))

  ;; This is the square-bracket [[X]] conversion from CwCC
  (define (cps exp K)
    (match exp with
      (clexp:lit n)
      -> (let ((x (genvar)))
           (cps-letval x n (K x)))
      (clexp:ref s)
      -> (K s)
      (clexp:set name exp)
      -> (raise (:NotImplemented (clexp->sexp exp)))
      (clexp:call name args)
      -> (let ((x (genvar))
               (k (gencont)))
           (cps-args args '()
             (if (member-eq? name prims)
                 (lambda (vars)
                   (cps-prim name x vars (K x)))
                 (lambda (vars)
                   (cps-letcont
                    k (list x) (K x)
                    (cps-app name k vars))))))
      (clexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()        -> (raise (:EmptySequence))
             (one)     -> (cps one K)
             (hd . tl) -> (cps hd (lambda (x1) (cps-dead (loop tl))))
             ))
      (clexp:let name type init body)
      -> (let ((j (gencont)))
           ;; XXX record type here
           (cps-letcont
            j (list name)
            (cps body K)
            (cps-tail init j)))
      (clexp:if test con ant)
      -> (let ((j (gencont))
               (x (genvar))
               (x1 (genvar))
               (x2 (genvar))
               (k1 (gencont))
               (k2 (gencont)))
           (cps
            test
            (lambda (z)
              (cps-letcont
               j (list x) (K x)
               (cps-letcont
                k1 (list x1) (cps-tail con j)
                (cps-letcont
                 k2 (list x2) (cps-tail ant j)
                 (cps-if z k1 k2))))))
           )
      (clexp:loop k binds body)
      -> (let (((vars0 inits) (zip binds))
               ((vars1 types) (zip vars0))
               (k0 (gencont))
               (x0 (genvar)))
           ;; XXX record var types
           (cps-args
            inits '()
            (lambda (vars2)
              (cps-letcont
               k vars2
               (cps-tail body k)
               (cps-letcont k0 (list x0) (K x0) (cps-appk k vars1))))))
      (clexp:appk k xs)
      -> (raise (:NonTailAppK))
      x
      -> (raise (:NotYet x))
      )
    )

  ;; This is the rounded-bracket ((X)) conversion from CwCC
  (define (cps-tail exp k)
    (match exp with
      (clexp:lit n)
      -> (let ((x (genvar)))
           (cps-letval x n (cps-appk k (list x))))
      (clexp:ref s)
      -> (cps-appk k (list s))
      (clexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()           -> (raise (:EmptySequence))
             (exp)        -> (cps-tail exp k)
             (exp . exps) -> (cps exp (lambda (x1) (cps-dead (loop exps))))
             ))
      (clexp:call name args)
      -> (cps-args
          args '()
          (if (member-eq? name prims)
              (lambda (vars)
                (let ((x (genvar)))
                  (cps-prim name x vars (cps-appk k (list x)))))
              (lambda (vars) (cps-app name k vars))))
      (clexp:let name type init body)
      -> (let ((j (gencont)))
           ;; XXX record type here
           (cps-letcont
            j (list name)
            (cps-tail body k)
            (cps-tail init j)))
      (clexp:if test con ant)
      -> (let ((x1 (genvar))
               (x2 (genvar))
               (k1 (gencont))
               (k2 (gencont)))
           (cps
            test
            (lambda (z)
             (cps-letcont
              k1 (list x1) (cps-tail con k)
              (cps-letcont
               k2 (list x2) (cps-tail ant k)
               (cps-if z k1 k2))))))
      (clexp:loop k0 binds body)
      -> (let (((vars0 inits) (zip binds))
               ((vars1 types) (zip vars0)))
           ;; XXX record types
           (cps-args
            inits '()
            (lambda (vars2)
              (cps-letcont
               k0 vars2
               (cps-tail body k)
               (cps-appk k0 vars1)))))
      (clexp:appk k vals)
      -> (cps-args vals '() (lambda (vars) (cps-appk k vars)))
      ;; XXX probably not
      (clexp:set name exp)
      -> (raise (:DeadTail))
      x
      -> (raise (:NotYet x))
      ))

  (cps-tail exp 'halt)

  )

