;; -*- Mode: Irken -*-


;; this will become vtype, and we'll probably have to have a way of defining
;;  literals.
(typealias val int)

;; (typealias var symbol)
;; (typealias cvar symbol)
(datatype var
  (:t symbol type)
  )
(datatype cvar
  (:t symbol)
  )
(define var/name (var:t name _) -> name)
(define var/type (var:t _ type) -> type)

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

;; perhaps this was muddled thinking.  Looking at CwCC, we can see that types
;;  are attached to: 1) values and 2) variables.  CwCC uses a special notation
;;  for "continuation accepting type x".  Our continuations are variadic, so what
;;  type we attach will also be a list - or perhaps, if every 'var' has an attached
;;  type then we get this 'for free'.  In other words, I think we might only need
;;  to expand the 'var' datatype to include a type. [would cvar then also have an
;;  attached type or do we 'look it up' in the environment?]

;; on second thought - we have both binding and reference, I think we want type
;;  only at the binding.  otherwise it's just a pain to deal with.
;;  so which arms do binding? prim, letval, letcont.

;; XXXXXXX letcont vars must have types!  so now I'm thinking back to
;;   the previous version of the var type, since it seems less
;;   inconvenient now, and (hand-waving here) would also be a natural
;;   place to attach src annotation.

(datatype cps
  (:prim symbol var (list var) cps)  ;; x + y
  (:letval var val cps)              ;; letval x = V in L
  (:letcont cvar (list var) cps cps) ;; letcont k x0 x1 ... = K in L
  (:appk cvar (list var))            ;; k x0 x1 ...
  (:app symbol cvar (list var))      ;; f k x0 x1 ...
  (:if var cvar cvar)                ;; if x k1 k2
  (:dead cps)                        ;; K (for seq)
  )

(define (dump-cps d exp)
  (define fvart  (var:t x t) -> (format (ansi green (sym x)) ":" (ftype t)))
  (define fvar   (var:t x t) -> (format (ansi green (sym x))))
  (define fcvar  (cvar:t x)  -> (format (ansi magenta (sym x))))
  (define ftype t            -> (format (ansi yellow (repr (type->sexp (apply-subst t))))))
  (define fname n            -> (format (ansi cyan (sym n))))
  (printf (repeat d "  "))
  (match exp with
    (cps:prim n x vars K)
    -> (begin
         (printf "prim " (fvart x) " = " (fname n) " " (join fvar " " vars) "\n")
         (dump-cps d K))
    (cps:letval x v K)
    -> (begin
         (printf "letval " (fvart x) " = " (int v) "\n")
         (dump-cps d K))
    (cps:letcont k xs K0 K1)
    -> (begin
         (printf "letcont " (fcvar k) " " (join fvart " " xs) "\n")
         (dump-cps (+ d 1) K0)
         (dump-cps d K1)
         )
    (cps:appk k xs)
    -> (printf "appk " (fcvar k) " " (join fvar " " xs) "\n")
    (cps:app n k xs)
    -> (printf "app " (fname n) " " (fcvar k) " " (join fvar " " xs) "\n")
    (cps:if t c a)
    -> (printf "if " (fvar t) " " (fcvar c) " " (fcvar a) "\n")
    (cps:dead K)
    -> (begin (printf "dead\n") (dump-cps d K))
    ))

(define (cps->sexp cps)
  (define (ST t) (type->sexp t))
  (define SV
    (var:t name type) -> (sexp (sym name) (ST type)))
  (define SCV
    (cvar:t name) -> (sexp (sym name)))
  (define S
    (cps:prim n x vars k)    -> (sexp (sym 'prim) (sym n) (SV x)
                                      (list (map SV vars))
                                      (S k))
    (cps:letval x v k)       -> (sexp (sym 'letval) (SV x) (int v) (S k))
    (cps:letcont k xs t0 t1) -> (sexp (sym 'letcont) (SCV k)
                                      (list (map SV xs))
                                      (S t0) (S t1))
    (cps:appk k xs)          -> (sexp (sym 'appk) (SCV k)
                                      (list (map SV xs)))
    (cps:app n k vars)       -> (sexp (sym 'app) (sym n) (SCV k)
                                      (list (map SV vars)))
    (cps:if tst c a)         -> (sexp (sym 'if) (SV tst) (SCV c) (SCV a))
    (cps:dead k)             -> (sexp (sym 'dead) (S k))
    )
  (S cps)
  )

;; this probably needs to be a map from name to type sig.
(define prims (list '+ '- '* '/ 'and 'or 'xor '<< '>> 'ashr '= '<> '< '> '<= '>=))

;; --------------
;; CPS conversion
;; --------------

(define (zexp->cps tenv exp)

  (define make-tvar
    (let ((counter 0))
      (lambda ()
        (inc! counter)
        (type/var counter))))

  (define (gensym prefix)
    (let ((counter 0))
      (lambda ()
        (inc! counter)
        (string->symbol (format prefix (int counter))))))

  (define genvar (gensym "r"))
  (define gencont (gensym "L"))
  (define (newvar) (var:t (genvar) (make-tvar)))
  (define (newcont) (cvar:t (gencont)))

  (define (cps-args env args vars K)
    (match args with
      ()        -> (K (reverse vars))
      (hd . tl) -> (cps env hd (lambda (v) (cps-args env tl (list:cons v vars) K)))
      ))

  (define (zip items)
    (define loop
      acc0 acc1 ()                    -> (:tuple (reverse acc0) (reverse acc1))
      acc0 acc1 ((:tuple a b) . rest) -> (loop (list:cons a acc0) (list:cons b acc1) rest)
      )
    (loop (list:nil) (list:nil) items))

  (define aztname->var
    (aztname:t name type src) -> (var:t name type)
    )

  (define (extend env var)
    (match var with
      (var:t name _) -> (alist:entry name var env)
      ))

  (define extend*
    env ()        -> env
    env (hd . tl) -> (extend* (extend env hd) tl)
    )

  (define (lookup-val env name)
    (alist/lookup env name))

  (define (lookup-type name)
    (match (alist/lookup tenv name) with
      (maybe:yes t) -> t
      (maybe:no)    -> (make-tvar)
      ))

  (define (valid-funcall? name nargs)
    (match (alist/lookup tenv name) with
      (maybe:yes (type:arrow rtype argtypes _))
      -> (= nargs (length argtypes))
      _
      -> #f
      ))

  ;; This is the square-bracket [[X]] conversion from CwCC
  (define cps
    ;; strip src annotation [for now]
    env (azexp:t exp src) K -> (cps* env exp K)
    )

  (define (cps* env exp K)
    (match exp with
      ;; currently only int.
      (zexp:lit n)
      -> (let ((x (newvar)))
           (cps:letval x n (K x)))
      (zexp:ref s)
      -> (match (lookup-val env s) with
           (maybe:yes v) -> (K v)
           ;; XXX require declarations of external funs.
           (maybe:no) -> (K (var:t s (lookup-type s))))
      ;; (zexp:set name v)
      ;; -> (raise (:NotImplemented exp))
      (zexp:call name args)
      -> (let ((x (newvar))
               (k (newcont)))
           (cps-args env args '()
             (if (or (member-eq? name prims) (valid-funcall? name (length args)))
                 (lambda (vars)
                   (cps:prim name x vars (K x)))
                 (lambda (vars)
                   (cps:letcont
                    k (list x) (K x)
                    (cps:app name k vars))))))
      (zexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()        -> (raise (:EmptySequence))
             (one)     -> (cps env one K)
             (hd . tl) -> (cps env hd (lambda (x1) (cps:dead (loop tl))))
             ))
      (zexp:let (aztname:t name type _) init body)
      -> (let ((j (newcont))
               (v (var:t name type)))
           (cps:letcont
            j (list v)
            (cps (extend env v) body K)
            (cps-tail env init j)))
      (zexp:if test con alt)
      -> (let ((j (newcont))
               (x (newvar))
               (k1 (newcont))
               (k2 (newcont)))
           (cps
            env test
            (lambda (z)
              (cps:letcont
               j (list x) (K x)
               (cps:letcont
                k1 (list) (cps-tail env con j)
                (cps:letcont
                 k2 (list) (cps-tail env alt j)
                 (cps:if z k1 k2)))))))
      (zexp:loop name binds body)
      -> (let (((vars0 inits) (zip binds))
               (vars1 (map aztname->var vars0))
               (kname (cvar:t name))
               (k0 (newcont))
               (x0 (newvar)))
           (cps-args
            (extend* env vars1)
            inits '()
            (lambda (vars2)
              (cps:letcont
               kname vars1
               (cps-tail (extend* env vars1) body k0)
               (cps:letcont
                k0 (list x0) (K x0)
                (cps:appk kname vars2))))))
      (zexp:appk k xs)
      -> (raise (:NonTailAppK))
      x
      -> (raise (:NotYet x))
      )
    )

  ;; This is the rounded-bracket ((X)) conversion from CwCC
  (define cps-tail
    env (azexp:t exp src) k -> (cps-tail* env exp k)
    )

  (define (cps-tail* env exp k)
    (match exp with
      (zexp:lit n)
      -> (let ((x (newvar)))
           (cps:letval x n (cps:appk k (list x))))
      (zexp:ref s)
      -> (cps:appk
          k (list
             (match (lookup-val env s) with
               (maybe:yes var) -> var
               (maybe:no) -> (var:t s (lookup-type s)))))
      ;; (zexp:set s v)
      ;; -> (raise (:NotImplemented exp))
      (zexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()           -> (raise (:EmptySequence))
             (exp)        -> (cps-tail env exp k)
             (exp . exps) -> (cps env exp (lambda (x1) (cps:dead (loop exps))))
             ))
      (zexp:call name args)
      -> (cps-args
          env args '()
          (if (or (member-eq? name prims) (valid-funcall? name (length args)))
              (lambda (vars)
                (let ((x (newvar)))
                  (cps:prim name x vars (cps:appk k (list x)))))
              (lambda (vars) (cps:app name k vars))))
      (zexp:let (aztname:t name type _) init body)
      -> (let ((j (newcont))
               (v (var:t name type)))
           (cps:letcont
            j (list v)
            (cps-tail (extend env v) body k)
            (cps-tail env init j)))
      (zexp:if test con alt)
      -> (let ((k1 (newcont))
               (k2 (newcont)))
           (cps
            env test
            (lambda (z)
             (cps:letcont
              k1 (list) (cps-tail env con k)
              (cps:letcont
               k2 (list) (cps-tail env alt k)
               (cps:if z k1 k2))))))
      (zexp:loop name binds body)
      -> (let (((vars0 inits) (zip binds))
               (vars1 (map aztname->var vars0))
               (kname (cvar:t name))
               )
           (cps-args
            (extend* env vars1) inits '()
            (lambda (vars2)
              (cps:letcont
               kname vars1
               (cps-tail (extend* env vars1) body k)
               (cps:appk kname vars2)))))
      (zexp:appk k vals)
      -> (cps-args env vals '() (lambda (vars) (cps:appk (cvar:t k) vars)))
      x
      -> (raise (:NotYet x))
      ))

  (cps-tail (alist:nil) exp (cvar:t 'halt))

  )

