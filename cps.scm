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
;; * <, >, etc.. (requires bool type tho, maybe)
;; * convert var/cvar to int
;;   (this turned out to be a Bad Idea - rewrite all hosed because no distinction)
;; * add functions (maybe?)
;;   Thought I needed functions for loops, but if instead I expose 'appk' to the user
;;     we can implement loops/recursion directly with conts.  I think.
;; * add types

(typealias var symbol)
(typealias cvar symbol)
(typealias val int)

(datatype cps
  (:let symbol var cps)         ;; let u = x in L
  (:ref symbol var cps)         ;; u
  (:set symbol var cps)         ;; set! u x
  (:prim symbol var (list var) cps) ;; x + y
  (:letval var val cps)         ;; letval x = V in L
  (:letcont cvar var cps cps)   ;; letcont k x = K in L
  (:appk cvar var)              ;; k x
  (:app symbol cvar (list var)) ;; f k x0 x1 ...
  (:if var cvar cvar)           ;; if x k1 k2
  (:dead cps)                   ;; K (for seq)
  )

(define cps->sexp
  (cps:let n x k)         -> (sexp (sym 'let) (sym n) (sym x) (cps->sexp k))
  (cps:ref n x k)         -> (sexp (sym 'ref) (sym n) (sym x) (cps->sexp k))
  (cps:set n x k)         -> (sexp (sym 'set) (sym n) (sym x) (cps->sexp k))
  (cps:prim n x vars k)   -> (sexp (sym 'prim) (sym n) (sym x) (list (map sexp:symbol vars)) (cps->sexp k))
  (cps:letval x v k)      -> (sexp (sym 'letval) (sym x) (int v) (cps->sexp k))
  (cps:letcont k x t0 t1) -> (sexp (sym 'letcont) (sym k) (sym x) (cps->sexp t0) (cps->sexp t1))
  (cps:appk k x)          -> (sexp (sym 'appk) (sym k) (sym x))
  (cps:app n k vars)      -> (sexp (sym 'app) (sym n) (sym k) (list (map sexp:symbol vars)))
  (cps:if t c a)          -> (sexp (sym 'if) (sym t) (sym c) (sym a))
  (cps:dead k)            -> (sexp (sym 'dead) (cps->sexp k))
  )

(define prims (list '+ '- '* '/ 'and 'or 'xor '<< '>> 'ashr '< '> '<= '>=))

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

  ;; This is the square-bracket [[X]] conversion from CwCC
  (define (cps exp K)
    (match exp with
      (clexp:lit n)
      -> (let ((x0 (genvar)))
           (cps:letval x0 n (K x0)))
      (clexp:ref s)
      -> (let ((x (genvar)))
           (cps:ref s x (K x)))
      (clexp:set name exp)
      -> (^bogus exp (lambda (z) (cps:set name z (K 'dead))))
      (clexp:call name args)
      -> (let ((x (genvar))
               (k (gencont)))
           (cps-args args '()
             (if (member-eq? name prims)
                 (lambda (vars)
                   (cps:prim name x vars (K x)))
                 (lambda (vars)
                   (cps:letcont k x (K x) (cps:app name k vars))))))
      (clexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()        -> (raise (:EmptySequence))
             (one)     -> (cps one K)
             (hd . tl) -> (cps hd (lambda (x1) (cps:dead (loop tl))))
             ))
      (clexp:let name init body)
      -> (let ((j (gencont))
               (x0 (genvar)))
           (cps:letcont
            j x0
            (cps:let name x0 (cps body K))
            (cps-tail init j)))
      (clexp:if test con ant)
      -> (let ((j (gencont))
               (x (genvar))
               (x1 (genvar))
               (x2 (genvar))
               (k1 (gencont))
               (k2 (gencont)))
           (^bogus
            test
            (lambda (z)
              (cps:letcont
               j x (K x)
               (cps:letcont
                k1 x1 (cps-tail con j)
                (cps:letcont
                 k2 x2 (cps-tail ant j)
                 (cps:if z k1 k2))))))
           )
      (clexp:loop k x init body)
      -> (let ((x0 (genvar)))
           (cps:letcont
            k x0
            (cps:let x x0 (cps init K))
            (cps-tail init k)))
      (clexp:appk k x)
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
           (cps:letval x n (cps:appk k x)))
      ;; (clexp:ref s)
      ;; -> (cps:appk k s)
      (clexp:ref s)
      -> (let ((x (genvar)))
           (cps:ref s x (cps:appk k x)))
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
                  (cps:prim name x vars (cps:appk k x))))
              (lambda (vars) (cps:app name k vars))))
      (clexp:let name init body)
      -> (let ((j (gencont))
               (x0 (genvar)))
           (cps:letcont
            j x0
            (cps:let name x0 (cps-tail body k))
            (cps-tail init j)))
      ;; (clexp:let name init body)
      ;; -> (let ((j (gencont)))
      ;;      (cps:letcont j name (cps-tail body k) (cps-tail init j)))
      (clexp:if test con ant)
      -> (let ((x1 (genvar))
               (x2 (genvar))
               (k1 (gencont))
               (k2 (gencont)))
           (^bogus
            test
            (lambda (z)
             (cps:letcont
              k1 x1 (cps-tail con k)
              (cps:letcont
               k2 x2 (cps-tail ant k)
               (cps:if z k1 k2))))))
      (clexp:loop k0 x init body)
      -> (let ((x0 (genvar)))
           (cps:letcont
            k0 x0
            (cps:let x x0 (cps-tail body k))
            (cps-tail init k0)))
      (clexp:appk k val)
      -> (^bogus val (lambda (v) (cps:appk k v)))
      ;; XXX probably not
      (clexp:set name exp)
      -> (raise (:DeadTail))
      x
      -> (raise (:NotYet x))
      ))

  ;; this is to work around a serious (but VERY RARE) problem with
  ;;   recursive calls.
  (define (^bogus exp K)
    (cps exp K))

  (cps-tail exp 'halt)

  )

;; --------------------------------------------------------------------------------
;; sample direct LLVM output.
;; --------------------------------------------------------------------------------

;; for this test I'm just going to emit text.
(define (cpsfun->llvm name args exp)

  (let ((phimap (alist:nil))
        (venv (alist:nil)))

    (define gensym
      (let ((counter 0))
        (lambda ()
          (inc! counter)
          (string->symbol (format "r" (int counter))))))

    (define (pass1 exp blockname)
      (match exp with
        (cps:let name x K)       -> (pass1 K blockname)
        (cps:ref name x K)       -> (pass1 K blockname)
        (cps:set name x K)       -> (pass1 K blockname)
        (cps:letval x V K)       -> (begin (alist/push venv x V) (pass1 K blockname))
        (cps:letcont k x K L)    -> (begin (pass1 L blockname) (pass1 K k))
        (cps:if x k1 k2)         -> #u
        (cps:appk k x)           -> (alist/push phimap k (:tuple x blockname))
        (cps:dead K)             -> (pass1 K blockname)
        (cps:prim name x vars K) -> (pass1 K blockname)
        (cps:app name k vars)    -> #u
        ))

    (define (emit-phi blockname x)
      (let loop ((acc (list:nil))
                 (phimap phimap))
        (match phimap with
          (alist:nil)
          -> (if (> (length acc) 0)
                 (printf "  %" (sym x) " = phi i64 [ " (join " ], [ " acc) " ]\n"))
          (alist:entry ktrg (:tuple x ksrc) rest)
          -> (if (eq? ktrg blockname)
                 (loop (list:cons (format (valref x) ", %" (sym ksrc)) acc) rest)
                 (loop acc rest))
          )))

    (define (valref x)
      (match (alist/lookup venv x) with
        (maybe:yes v) -> (format (int v))
        (maybe:no)    -> (format "%" (sym x))
        ))

    (define (emit exp blockname)
      (match exp with
        (cps:let name x K)
        -> (begin
             (printf "  %u" (sym name) " = alloca i64\n")
             (printf "  store i64 " (valref x) ", i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:ref name x K)
        -> (begin
             (printf "  %" (sym x) " = load i64, i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:set name x K)
        -> (begin
             (printf "  store i64 " (valref x) ", i64* %u" (sym name) "\n")
             (emit K blockname))
        (cps:letval x V K)
        -> (emit K blockname)
        (cps:letcont k x K L)
        -> (begin
             (emit L blockname)
             ;; note: L is the init, and is in the current block
             (printf "\n" (sym k) ":\n") ;; label
             (emit-phi k x)              ;; [ %x4, %block ]
             (emit K k)                  ;; with new blockname
             )
        (cps:if x k1 k2)
        -> (let ((r (gensym)))
             (printf "  %" (sym r) " = icmp ne i64 " (valref x) ", 0\n")
             (printf "  switch i1 %" (sym r) ", label %" (sym k1) " [i1 0, label %" (sym k2) "]\n"))
        (cps:appk k x)
        -> (branch k x blockname)
        (cps:dead K)
        -> (emit K blockname)
        (cps:prim name x vars K)
        -> (begin
             (emit-prim name x vars)
             (emit K blockname))
        (cps:app name k vars)
        -> (let ((r (gensym)))
             (printf "  %" (sym r) " = call i64 @" (sym name) " ("
                     (join (lambda (x) (format "i64 " (valref x))) ", " vars)
                     ")\n")
             (branch k r blockname))
        )
      )

    ;; phimap must be done in a separate pass.

    (define (branch k x blockname)
      (match k with
        'halt -> (printf "  ret i64 " (valref x) "\n")
        k     -> (printf "  br label %" (sym k) "\n")
        ))

    (define translate-prim
      ;; XXX this should probably be a formatting function so we can translate
      ;;     prims into multiple lines if necessary. (like "<" & ">", though those
      ;;     require a typed cps for i1).
      '+    -> "add"
      '-    -> "sub"
      '*    -> "mul"
      '/    -> "udiv"
      'and  -> "and"
      'or   -> "or"
      'xor  -> "xor"
      'ashr -> "ashr"
      '<<   -> "shl"
      '>>   -> "shr"
      x  -> (raise (:UnknownPrim x))
      )

    (define (emit-prim name x vars)
      (printf "  %" (sym x) " = " (translate-prim name) " i64 "
              (join valref ", " vars)
              "\n"))

    (printf "define i64 @" (sym name) "("
            (join (lambda (x) (format "i64 %u" (sym x))) ", " args)
            ") {\n")
    (printf "top:\n")
    (pass1 exp 'top)
    (emit exp 'top)
    (printf "}\n")
    )
  )
