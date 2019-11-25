;; -*- Mode: Irken -*-

;; this will become zlit
(typealias val int)

;; a normal variable
(datatype var
  (:t symbol type)
  )
;; a continuation variable.
(datatype cvar
  (:t symbol)
  )
(define var/name (var:t name _) -> name)
(define var/type (var:t _ type) -> type)

(datatype cps
  (:prim symbol sexp var (list var) cps) ;; x + y
  (:letval var zlit cps)                 ;; letval x = V in L
  (:letcont cvar (list var) cps cps)     ;; letcont k x0 x1 ... = K in L
  (:appk cvar (list var))                ;; k x0 x1 ...
  (:app symbol cvar (list var))          ;; f k x0 x1 ...
  (:if var cvar cvar)                    ;; if x k1 k2
  (:dead cps)                            ;; K (for seq)
  )

(define (dump-cps d exp)
  (define fvart  (var:t x t) -> (format (ansi green (sym x)) ":" (ftype t)))
  (define fvar   (var:t x t) -> (format (ansi green (sym x))))
  (define fcvar  (cvar:t x)  -> (format (ansi magenta (sym x))))
  (define ftype t            -> (format (ansi yellow (repr (type->sexp (apply-subst t))))))
  (define fname n            -> (format (ansi cyan (sym n))))
  (printf (repeat d "  "))
  (match exp with
    (cps:prim n p x vars K)
    -> (begin
         (printf "prim " (fvart x) " = " (fname n) " " (repr p) " " (join fvart " " vars) "\n")
         (dump-cps d K))
    (cps:letval x v K)
    -> (begin
         (printf "letval " (fvart x) " = " (zlit-repr v) "\n")
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
    (cps:prim n p x vars k)  -> (sexp (sym 'prim) (sym n) p (SV x)
                                      (list (map SV vars))
                                      (S k))
    (cps:letval x v k)       -> (sexp (sym 'letval) (SV x) (zlit->sexp v) (S k))
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

(define (alist/has-key? a k)
  (match (alist/lookup a k) with
    (maybe:yes _) -> #t
    (maybe:no)    -> #f
    ))

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
  (define (newdead) (var:t (genvar) (type:none)))
  (define (newcont) (cvar:t (gencont)))

  (define (cps-args env args vars K)
    (match args with
      ()        -> (K (reverse vars))
      (hd . tl) -> (cps
                    env hd
                    (lambda (v)
                      (cps-args env tl (list:cons v vars) K)))
      ))

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
      (maybe:yes (type:arrow rtype argtypes))
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
      (zexp:lit zlit)
      -> (let ((x (newvar)))
           (cps:letval x zlit (K x)))
      (zexp:ref s)
      -> (match (lookup-val env s) with
           (maybe:yes v) -> (K v)
           ;; XXX require declarations of external funs.
           (maybe:no) -> (K (var:t s (lookup-type s))))
      (zexp:prim name param args)
      -> (let ((x (newvar)))
           (cps-args
            env args '()
            (lambda (vars)
              (cps:prim name param x vars (K x)))))
      (zexp:call name args)
      -> (let ((x (newvar))
               (k (newcont)))
           (cps-args
            env args '()
            (if (or (alist/has-key? prim-type-map name)
                    (valid-funcall? name (length args)))
                (lambda (vars)
                  (cps:prim name (sexp:bool #f) x vars (K x)))
                (lambda (vars)
                  (cps:letcont
                   k (list x) (K x)
                   (cps:app name k vars))))))
      (zexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()           -> (raise (:EmptySequence))
             (exp)        -> (cps env exp K)
             (exp . exps) -> (let ((j (newcont)))
                               (cps:letcont
                                j (list (newdead))
                                (loop exps)
                                (cps-tail env exp j)))
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
                k1 '() (cps-tail env con j)
                (cps:letcont
                 k2 '() (cps-tail env alt j)
                 (cps:if z k1 k2)))))))
      (zexp:loop name binds body)
      -> (let (((vars0 inits) (unzip binds))
               (vars1 (map aztname->var vars0))
               (kname (cvar:t name))
               (k0 (newcont))
               (x0 (newvar)))
           (cps-args
            (extend* env vars1) inits '()
            (lambda (vars2)
              (cps:letcont
               kname vars1
               (cps-tail (extend* env vars1) body k0)
               (cps:letcont
                k0 (list x0) (K x0)
                (cps:appk kname vars2))))))
      ;; we want BOTH kbody and lbody to proceed
      ;;   to K, the surrounding context.
      (zexp:letcont name vars kbody lbody)
      -> (let ((k (newcont))
               (r (newvar))
               (kname (cvar:t name))
               (vars0 (map aztname->var vars)))
           (cps:letcont
            k (list r) (K r)
            (cps:letcont
             kname vars0
             (cps-tail (extend* env vars0) kbody k)
             (cps-tail env lbody k))))
      (zexp:appk k xs)
      -> (raise (:NonTailAppK))
      )
    )

  ;; bit of a hack here.  transparently change
  ;; (zexp:ref x) => (%prim '%get #f x)
  ;; this is probably the wrong place/way to do this?
  (define (frob-ref s)
    (zexp:prim '%get (sexp:undef) (list (azexp:t (zexp:ref s) null-src))))

  ;; This is the rounded-bracket ((X)) conversion from CwCC
  (define cps-tail
    env (azexp:t exp src) k -> (cps-tail* env exp k)
    )

  (define (cps-tail* env exp k)
    (match exp with
      (zexp:lit zlit)
      -> (let ((x (newvar)))
           (cps:letval x zlit (cps:appk k (list x))))
      (zexp:ref s)
      -> (match (lookup-val env s) with
           (maybe:yes var) -> (cps:appk k (list var))
           (maybe:no)
           -> (match (lookup-type s) with
                (type:ref t) -> (cps-tail* env (frob-ref s) k)
                (type:mut t) -> (cps-tail* env (frob-ref s) k)
                t -> (cps:appk k (list (var:t s t)))
                ))
      (zexp:prim name param args)
      -> (let ((x (newvar)))
           (cps-args
            env args '()
            (lambda (vars)
              (cps:prim name param x vars (cps:appk k (list x))))))
      (zexp:seq exps)
      -> (let loop ((exps exps))
           (match exps with
             ()           -> (raise (:EmptySequence))
             (exp)        -> (cps-tail env exp k)
             (exp . exps) -> (let ((j (newcont)))
                               (cps:letcont
                                j (list (newdead))
                                (loop exps)
                                (cps-tail env exp j)))
             ))
      (zexp:call name args)
      -> (cps-args
          env args '()
          (if (or (alist/has-key? prim-type-map name)
                  (valid-funcall? name (length args)))
              (lambda (vars)
                (let ((x (newvar)))
                  (cps:prim name (sexp:bool #f) x vars (cps:appk k (list x)))))
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
      -> (let (((vars0 inits) (unzip binds))
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
      (zexp:letcont name vars kbody lbody)
      -> (let ((vars0 (map aztname->var vars))
               (kname (cvar:t name)))
           (cps:letcont
            kname vars0
            (cps-tail (extend* env vars0) kbody k)
            (cps-tail env lbody k)))
      (zexp:appk k vals)
      -> (cps-args env vals '() (lambda (vars) (cps:appk (cvar:t k) vars)))
      ))

  (cps-tail (alist:nil) exp (cvar:t 'halt))

  )

