;; -*- Mode: Irken -*-

;; new implementation of mbe.

;; from in-progress work on irken: I think this is in a working state,
;;   but obviously needs some work to be useful.

;; "Macro-by-Example: Deriving Syntactic Transformations from their Specifications"
;; by Kohlbecker and Wand, popl-87.
;; https://doi.org/10.1145/41625.41632

(require "lib/basis.scm")
(require "./read.scm")
(require "lib/partial.scm")

;; this code is derived directly from "Section 3: Semantics"

;; sexp-pattern datatype: this represents a 'parsed' version
;; of an s-expression pattern, with preserved annotations.

(datatype sexpat
  (:exp sexp)
  (:var symbol)
  (:rep sexpat)
  (:ann sexp sexpat)
  (:list (list sexpat))
  )

(define sexpat-repr
  (sexpat:exp e)   -> (repr e)
  (sexpat:var s)   -> (format "$" (sym s))
  (sexpat:rep p)   -> (format (sexpat-repr p) " ...")
  (sexpat:ann a s) -> (format "[" (sexpat-repr s) "]")
  (sexpat:list ps) -> (format "(" (join sexpat-repr " " ps) ")")
  )

;; --- convert an sexp to a sexpat ---

(define (sexp->sexpat e)

  (define (bracket-check sym)
    (let ((s (symbol->string sym))
	  (slen (string-length s)))
      (match (string-ref s 0) (string-ref s (- slen 1)) with
        #\< #\> -> (sexpat:exp (sexp:symbol (string->symbol (substring s 1 (- slen 1)))))
        _ _     -> (sexpat:var sym)
        )))

  (define C
    (sexp:list ((sexp:symbol '%ann) a x)) -> (sexpat:ann a (C x))
    (sexp:list xs)   -> (sexpat:list (C* '() xs))
    (sexp:symbol s)  -> (bracket-check s)
    other            -> (sexpat:exp other)
    )

  (define dot3?
    (sexp:list ((sexp:symbol '%ann) a (sexp:symbol '...))) -> #t
    (sexp:symbol '...) -> #t
    _ -> #f
    )

  (define C*
    acc ()        -> (reverse acc)
    acc (hd . tl) -> (if (dot3? hd)
                         (C* (list:cons (sexpat:rep (first acc)) (rest acc)) tl)
                         (C* (list:cons (C hd) acc) tl))
    )

  (C e)
  )

;; --- test a pattern against an input ---

(define B
  p (sexp:list ((sexp:symbol '%ann) _ e)) -> (B p e)
  (sexpat:exp a) b                        -> (sexp=? a b)
  (sexpat:var s) _                        -> #t
  (sexpat:ann a s) x                      -> (B s x)
  (sexpat:list al) (sexp:list bl)         -> (B* al bl)
  (sexpat:list al) exp                    -> (raise (:Nope3))
  (sexpat:rep p) exp                      -> (impossible)
  )

(define B*
  () ()                       -> #t
  ((sexpat:rep p) . ptl) exps -> (all? (partial (B p _)) exps)
  (phd . ptl) (ehd . etl)     -> (and (B phd ehd) (B* ptl etl))
  _ _                         -> #f
  )

;; --- return an environment binding pattern variables on an input ---

(define D
  (sexpat:var s) e                -> (alist:entry s (:tuple 0 e) (alist:nil))
  (sexpat:ann a p) e              -> (D p e)
  p (sexp:list ((sexp:symbol '%ann) _ e)) -> (D p e) ;; skip annotations
  (sexpat:list al) (sexp:list bl) -> (D* al bl)
  a b                             -> (raise (:Nope1 (sexpat-repr a) (repr b)))
  )

(define D*
  () ()                       -> (alist:nil)
  ((sexpat:rep p) . ptl) exps -> (combine-envs (map (partial (D p _)) exps))
  (phd . ptl) (ehd . etl)     -> (env-union (D phd ehd) (D* ptl etl))
  a b                         -> (raise (:Nope2 (sexpat-repr (sexpat:list a)) (repr (sexp:list b))))
  )

;; note: assumes no variable conflicts
(define env-union
  (alist:nil) env -> env
  env (alist:nil) -> env
  (alist:entry k0 v0 e0) (alist:entry k1 v1 e1)
  -> (alist:entry k0 v0 (alist:entry k1 v1 (env-union e0 e1)))
  )

;; p=(x y); envs = ({x=(1,a) y=(1,b)} {x=(1,c) y=(1,d)} ...)
;; =>
;; {x=(2,(a c ...)) y=(2,(b d ...))}
(define (combine-envs envs)
  (let ((result (alist:nil))
        (env0 (first envs)))
    (for-alist k0 v0 env0
      (match v0 with
        (:tuple level0 val0)
        -> (let ((vals (list val0)))
             (for-list env1 (rest envs)
               (match (alist/lookup env1 k0) with
                 (maybe:yes (:tuple level1 val1))
                 -> (push! vals val1)
                 (maybe:no)
                 -> (impossible)
                 ))
             (alist/push result
                         k0
                         (:tuple (+ level0 1)
                                 (sexp:list (reverse vals)))))))
    result))

(define (print-env env)
  (printf "env {\n")
  (for-alist k v env
    (match v with
      (:tuple lev val)
      -> (printf " " (sym k) ": " (int lev) ", " (repr val) "\n")))
  (printf "}\n")
  )

;; --- apply an environment to an output pattern ---

(define T
  env (sexpat:ann a p) -> (list (sexp (sym '%ann) a (first (T env p))))
  env (sexpat:var s)   -> (list (apply-env env s))
  env (sexpat:list l)  -> (list (sexp:list (T* env l)))
  env (sexpat:exp e)   -> (list e)
  env (sexpat:rep p)   -> (Trep env p)
  )

(define T*
  env ()        -> '()
  env (hd . tl) -> (append (T env hd) (T* env tl))
  )

(define (apply-env env s)
  (match (alist/lookup env s) with
    (maybe:no) -> (sexp:symbol s)
    (maybe:yes (:tuple 0 val)) -> val
    (maybe:yes (:tuple n val)) -> (raise (:MBE/Fnord (repr (sexp (sym s) (int n) val))))
    ))

(define (Trep env p)

  ;; restrict env to free variables in p
  (define (fv env p)
    (let ((result (alist:nil)))
      (define W
        (sexpat:rep p)   -> (W p)
        (sexpat:ann a p) -> (W p)
        (sexpat:list ps) -> (W* ps)
        (sexpat:exp e)   -> #u
        (sexpat:var s)
        -> (match (alist/lookup env s) with
             (maybe:yes val) -> (alist/push result s val)
             (maybe:no)      -> #u))
      (define W*
        ()        -> #u
        (hd . tl) -> (begin (W hd) (W* tl))
        )

      (W p)
      result
      ))

  ;; "We then check whether the variables of p include at least one
  ;;   variable of level greater than 0."

  (define controllable
    (alist:entry k (:tuple 0 v) env) -> (controllable env)
    (alist:entry k (:tuple _ _) _)    -> #t
    (alist:nil)                       -> #f
    )

  (define (check-lengths env)
    (define plen
      (:tuple 0 _)             -> 0
      (:tuple n (sexp:list l)) -> (length l)
      _                        -> (impossible))
    (let ((lengths (filter >0 (map plen (alist->values env)))))
      (when (not (all? (lambda (x) (= (first lengths) x)) (rest lengths)))
        (raise (:MBE/UnequalLengths env)))))

  ;; input:
  ;; env {
  ;;  m: 1, (j k)
  ;;  i: 1, (a b)
  ;; }
  ;; output:
  ;; env {m:(0,j) i:(0,a)}
  ;; env {m:(0,k) i:(0,b)}

  (define decompose
    acc0 acc1 (alist:nil)
    -> (maybe:yes (:tuple acc0 acc1))
    acc0 acc1 (alist:entry k (:tuple 0 val) env)
    -> (decompose (alist:entry k (:tuple 0 val) acc0)
                  (alist:entry k (:tuple 0 val) acc1)
                  env)
    acc0 acc1 (alist:entry k (:tuple lev (sexp:list ())) env)
    -> (maybe:no)
    acc0 acc1 (alist:entry k (:tuple lev (sexp:list (val . vals))) env)
    -> (decompose (alist:entry k (:tuple (- lev 1) val) acc0)
                  (alist:entry k (:tuple lev (sexp:list vals)) acc1)
                  env)
    _ _ env
    -> (raise (:MBE/UnequalLengths env))
    )

  (define append*
    acc ()        -> (reverse acc)
    acc (hd . tl) -> (append* (fold list:cons acc hd) tl)
    )

  (let ((env0 (fv env p)))
    (when (not (controllable env0))
      (raise (:MBE/BadOutputPattern (sexpat-repr p))))
    (check-lengths env0)
    (let loop ((env1 env0)
               (result '()))
      (match (decompose (alist:nil) (alist:nil) env1) with
        (maybe:yes (:tuple hdenv tlenv))
        -> (loop tlenv (list:cons hdenv result))
        (maybe:no)
        -> (append* '() (map (partial (T _ p)) (reverse result)))
        ))))

;; --- apply macro ---

(define (A p o i)
  (printf "p " (sexpat-repr p) "\n")
  (printf "o " (sexpat-repr o) "\n")
  (let ((env (D p i))
        (e (first (T env o))))
    (print-env env)
    (pp e 80)
    (pp (remove-annotations e) 80)
    ))

;; sexp-match

;; what do we want it to look like?
;; best case: just like normal pattern-matching?
;; (sexp-match thing with
;;   (thing $x ...) -> (format (join repr $x))
;;   ...)
;;
;; how about a practical usage?
;; for example, splitting a <body> into defines and not-defines?

;; a practical use of sexp-match is to replace 'normal' sexp matches
;; with ones that:
;; 1) preserve/ignore %annotations.
;; 2) simplify the match patterns.
;;
;; with that, I think it might be possible to replace bits of
;;  transform.scm piecemeal, as a test.
;;

;; --- testing ---

(define (read2-string s annotate?)
  (read2 "<string>" (string-reader s) annotate?))


(define (test-C s)
  (let ((r (sexp->sexpat (first (read2-string s #f)))))
    (printf (sexpat-repr r) "\n")
    ))

(define (test-B s)
  (match (read2-string s #t) with
    (p i) -> (begin
               (printf "pat : " (sexpat-repr (sexp->sexpat p)) "\n")
               (printf "B? " (bool (B (sexp->sexpat p) i)) "\n"))
    _     -> (raise (:Nope))
    ))

(define (test-D s)
  (match (read2-string s #t) with
    (p i) -> (print-env (D (sexp->sexpat p) i))
    _     -> (raise (:Nope))
    ))

(define (test-A s)
  (match (read2-string s #t) with
    (p o i) -> (A (sexp->sexpat p) (sexp->sexpat o) i)
    _       -> (raise (:Nope))
    ))

;; (test-C "(bar x ... ... y ... ...)")
;; (test-C "(bar (a b) ... (c d) ...)")
;; (test-C "(bar a ... b)")
;; (test-C "(thing x ...)")
;; (test-C "(foo ((x  y) ...) ...)")

;; (test-B "(thing a b c) (thing 1 2 3)")
;; (test-B "(thing x ...) (thing 1 2 3)")

;; (test-B "(<thing> a b c) (thing 1 2 3)")
;; (test-B "(<thing> x ...) (thing 1 2 3)")

;; (test-D "(thing ((x y) ...) ...) (thing ((1 2) (3 4)) ((5 6) (7 8)))")

;; (test-A
;;  "(let ((i e) ...) b ...)
;;   ((lambda (i ...) b ...) e ...)
;;   (let ((x 3) (y 4)) (+ x y))")

;; (test-A
;;  "(foo ((i j) ...) ((m n) ...))
;;   (bar (i m) ... (j n) ...)
;;   (foo ((1 2) (3 4)) ((5 6) (7 8)))")

;; (test-A
;; "(foo ((x  y) ...) ...)
;;  (bar x ... ... y ... ...)
;;  (foo ((1 2) (3 4)) ((5 6) (7 8)))")

;; (test-A
;; "(begin (begin x ...) y ...)
;;  (begin x ... y ...)
;;  (begin (begin 1 2 3) 4 5 6)")

;; (test-A
;;  "(foo ((i j) ...) ((m n) ...))
;;   (bar (i m) ... (j n) ...)
;;   (foo ((1 2) (3 4) (#(1) #(2))) ((5 6) (7 8) (9 10)))")

;; (test-A
;;  "(foo ((i j) ...) ((m n) ...))
;;   (bar (* (+ i m) (- j n)) ...)
;;   (foo ((1 2) (3 4)) ((5 6) (7 8)))")

;; (test-A
;;  "(foo (i j k) ...)
;;   (bar (* (- k (+ j i)) ...))
;;   (foo ((1 2 3) (4 5 6) (7 8 9)))")

;; (test-A
;;  "(foo (i j k) ...)
;;   (bar (* (- k (+ j i)) ...))
;;   (foo (1 2 3) (4 5 6) (7 8 9))")

(test-A
 "(zoo (((p0 ...) e) ...))
  (moo (p0 ... -> e) ...)
  (zoo (((a b c) 0) ((a b) 1)))")


