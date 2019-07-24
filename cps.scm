;; -*- Mode: Irken -*-

;; TODO
;; * either:
;;   1) make letcont n-ary (so we can do full "let loop")
;;      pro: SSA supports multiple phi, so should we?
;;      con: rewrite/etc maybe too complex.
;;   2) implement tuples as in ML/CwCC
;;      pro: all cps remains simple
;;      con: we have to convert to/from tuple repr for
;;           nary functions and conts.
;; * get rid of let/ref/set.  the right way to do this is to
;;   extend the universe of values to include 'ref' values, then just
;;   use letval. set! becomes a prim.  but I'm pretty sure this
;;   requires types.
;; * convert var/cvar to int
;;   (this turned out to be a Bad Idea - rewrite all hosed because no distinction)
;;   might want to explore this again later using a real datatype for the various
;;   var types.
;; * add functions (maybe?)
;;   Thought I needed functions for loops, but if instead I expose 'appk' to the user
;;     we can implement loops/recursion directly with conts.  I think.
;; * add types

(typealias var symbol)
(typealias cvar symbol)
(typealias val int)

(datatype cps
  (:prim symbol var (list var) cps)  ;; x + y
  (:letval var val cps)              ;; letval x = V in L
  (:letcont cvar (list var) cps cps) ;; letcont k x0 x1 ... = K in L
  (:appk cvar (list var))            ;; k x0 x1 ...
  (:app symbol cvar (list var))      ;; f k x0 x1 ...
  (:if var cvar cvar)                ;; if x k1 k2
  (:dead cps)                        ;; K (for seq)
  )

(define cps->sexp
  (cps:prim n x vars k)    -> (sexp (sym 'prim) (sym n) (sym x)
                                    (list (map sexp:symbol vars))
                                    (cps->sexp k))
  (cps:letval x v k)       -> (sexp (sym 'letval) (sym x) (int v) (cps->sexp k))
  (cps:letcont k xs t0 t1) -> (sexp (sym 'letcont) (sym k)
                                    (list (map sexp:symbol xs))
                                    (cps->sexp t0) (cps->sexp t1))
  (cps:appk k xs)          -> (sexp (sym 'appk) (sym k)
                                    (list (map sexp:symbol xs)))
  (cps:app n k vars)       -> (sexp (sym 'app) (sym n) (sym k)
                                    (list (map sexp:symbol vars)))
  (cps:if t c a)           -> (sexp (sym 'if) (sym t) (sym c) (sym a))
  (cps:dead k)             -> (sexp (sym 'dead) (cps->sexp k))
  )

(define prims (list '+ '- '* '/ 'and 'or 'xor '<< '>> 'ashr '= '<> '< '> '<= '>=))

;; --------------
;; CPS conversion
;; --------------

(define (clexp->cps exp)

  (define (gensym prefix)
    (let ((counter 0))
      (lambda ()
        (inc! counter)
        (string->symbol (format prefix (int counter))))))

  (define genvar (gensym "x"))
  (define gencont (gensym "L"))

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
           (cps:letval x n (K x)))
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
                   (cps:prim name x vars (K x)))
                 (lambda (vars)
                   (cps:letcont k (list x) (K x) (cps:app name k vars))))))
      (clexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()        -> (raise (:EmptySequence))
             (one)     -> (cps one K)
             (hd . tl) -> (cps hd (lambda (x1) (cps:dead (loop tl))))
             ))
      (clexp:let name init body)
      -> (let ((j (gencont)))
           (cps:letcont
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
              (cps:letcont
               j (list x) (K x)
               (cps:letcont
                k1 (list x1) (cps-tail con j)
                (cps:letcont
                 k2 (list x2) (cps-tail ant j)
                 (cps:if z k1 k2))))))
           )
      ;; XXX a brain-twister, this.  ok, I think we need to look
      ;;   at how <inits> are done.  I think we might need to consider
      ;;   how an <init> finishes with an <appk>.  In our case we want
      ;;   the inits (plural) to finish with (appk k x0 x1 ...).  we need
      ;;   to go _back_ and see how complex inits & args are put together
      ;;   _before_ we made all this change.
      (clexp:loop k binds body)
      -> (let (((vars inits) (zip binds))
               (k0 (gencont))
               (x0 (genvar)))
           (cps-args
            inits '()
            (lambda (vars0)
              (cps:letcont
               k vars
               (cps-tail body k)
               (cps:letcont k0 (list x0) (K x0) (cps:appk k vars0))))))
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
           (cps:letval x n (cps:appk k (list x))))
      (clexp:ref s)
      -> (cps:appk k (list s))
      (clexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()
             -> (raise (:EmptySequence))
             (exp)
             -> (cps-tail exp k)
             (exp . exps)
             -> (cps exp (lambda (x1) (cps:dead (loop exps))))
             ))
      (clexp:call name args)
      -> (cps-args
          args '()
          (if (member-eq? name prims)
              (lambda (vars)
                (let ((x (genvar)))
                  (cps:prim name x vars (cps:appk k (list x)))))
              (lambda (vars) (cps:app name k vars))))
      (clexp:let name init body)
      -> (let ((j (gencont)))
           (cps:letcont
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
             (cps:letcont
              k1 (list x1) (cps-tail con k)
              (cps:letcont
               k2 (list x2) (cps-tail ant k)
               (cps:if z k1 k2))))))
      (clexp:loop k0 binds body)
      -> (let (((vars inits) (zip binds)))
           (cps-args
            inits '()
            (lambda (vars0)
              (cps:letcont
               k0 vars
               (cps-tail body k)
               (cps:appk k0 vars0)))))
      (clexp:appk k vals)
      -> (cps-args vals '() (lambda (vars) (cps:appk k vars)))
      ;; XXX probably not
      (clexp:set name exp)
      -> (raise (:DeadTail))
      x
      -> (raise (:NotYet x))
      ))

  (cps-tail exp 'halt)

  )

