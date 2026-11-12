;; -*- Mode: Irken -*-

;; new implementation of mbe.

;; originally from in-progress work for irken.
;;
;; XXX this does not [yet] handle $var unique-ing.
;; XXX consider using (QUOTE literal) rather than <literal>,
;;     it's certainly more lisp and less kludge.  [though it then makes
;;     using quotes in macros impossible.  probably of no consequence
;;     for gaz.]

;; "Macro-by-Example: Deriving Syntactic Transformations from their Specifications"
;; by Kohlbecker and Wand, popl-87.
;; https://doi.org/10.1145/41625.41632

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
  (sexpat:exp e)   -> (format "<" (repr e) ">")
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
        #\< #\> -> (sexpat:exp (sexp:symbol (string->symbol (substring s 1 (- slen 1))) null-src))
        _ _     -> (sexpat:var sym)
        )))

  (define C
    (sexp:list ((sexp:symbol '%ann _) a x) _) -> (sexpat:ann a (C x))
    (sexp:list xs _)   -> (sexpat:list (C* '() xs))
    (sexp:symbol s _)  -> (bracket-check s)
    other            -> (sexpat:exp other)
    )

  (define dot3?
    (sexp:list ((sexp:symbol '%ann _) a (sexp:symbol '... _)) _) -> #t
    (sexp:symbol '... _) -> #t
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

(define (macro/test-one? ipat input)
  ;; --- test a pattern against an input ---

  (define B
    p (sexp:list ((sexp:symbol '%ann _) _ e) _) -> (B p e)
    (sexpat:exp a) b                        -> (sexp=? a b)
    (sexpat:var s) _                        -> #t
    (sexpat:ann a s) x                      -> (B s x)
    (sexpat:list al) (sexp:list bl _)         -> (B* al bl)
    (sexpat:list al) exp                    -> #f
    (sexpat:rep p) exp                      -> (impossible)
    )

  (define B*
    () ()                       -> #t
    ((sexpat:rep p) . ptl) exps -> (all? (partial (B p _)) exps)
    (phd . ptl) (ehd . etl)     -> (and (B phd ehd) (B* ptl etl))
    _ _                         -> #f
    )

  (B ipat input)
  )

(define (macro/apply-one ipat opat input)

  ;; --- return an environment binding pattern variables on an input ---

  (define D
    (sexpat:var s) e                        -> (alist:entry s (:tuple 0 e) (alist:nil))
    (sexpat:ann a p) e                      -> (D p e)
    p (sexp:list ((sexp:symbol '%ann _) _ e) _) -> (D p e) ;; skip annotations
    (sexpat:list al) (sexp:list bl _)         -> (D* al bl)
    (sexpat:exp a) b                        -> (alist:nil)
    a b                                     -> (raise (:Nope1 (sexpat-repr a) (repr b)))
    )

  (define D*
    () ()                       -> (alist:nil)
    ;; XXX there is a problem here where exps is null.
    ;;  seems to happen with patterns like (e1 e2 ...) where there's only
    ;;  e1 and no e2.  the call to `first` fails in combine-envs.
    ((sexpat:rep p) . ptl) exps -> (combine-envs (map (partial (D p _)) exps))
    (phd . ptl) (ehd . etl)     -> (env-union (D phd ehd) (D* ptl etl))
    a b                         -> (raise (:Nope2 (sexpat-repr (sexpat:list a)) (repr (sexp:list b null-src))))
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
                                   (sexp:list (reverse vals) null-src))))))
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
    env (sexpat:list l)  -> (list (sexp:list (T* env l) null-src))
    env (sexpat:exp e)   -> (list e)
    env (sexpat:rep p)   -> (Trep env p)
    )

  (define T*
    env ()        -> '()
    env (hd . tl) -> (append (T env hd) (T* env tl))
    )

  (define (apply-env env s)
    (match (alist/lookup env s) with
      (maybe:no) -> (sexp:symbol s null-src)
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

    (define controllable?
      (alist:entry k (:tuple 0 v) env) -> (controllable? env)
      (alist:entry k (:tuple _ _) _)   -> #t
      (alist:nil)                      -> #f
      )

    (define (check-lengths env)
      (define plen
        (:tuple 0 _)             -> 0
        (:tuple n (sexp:list l _)) -> (length l)
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
      acc0 acc1 (alist:entry k (:tuple lev (sexp:list () _)) env)
      -> (maybe:no)
      acc0 acc1 (alist:entry k (:tuple lev (sexp:list (val . vals) _)) env)
      -> (decompose (alist:entry k (:tuple (- lev 1) val) acc0)
                    (alist:entry k (:tuple lev (sexp:list vals null-src)) acc1)
                    env)
      _ _ env
      -> (raise (:MBE/UnequalLengths env))
      )

    (define append*
      acc ()        -> (reverse acc)
      acc (hd . tl) -> (append* (fold list:cons acc hd) tl)
      )

    (let ((env0 (fv env p)))
      (when (not (controllable? env0))
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

  ;; (printf "ipat " (sexpat-repr ipat) "\n")
  ;; (printf "opat " (sexpat-repr opat) "\n")
  (let ((env (D ipat input))
        (e (first (T env opat))))
    ;; (print-env env)
    ;; (pp e 80)
    ;; (pp (remove-annotations e) 80)
    e
    ))

(define (macro/parse pairs)
  ;; --- parse a defmacro ---
  ;; XXX how to handle syntax errors in macro definitions
  (define parse
    ;; assumes the 'defmacro' symbol has been removed.
    acc ()
    -> (reverse acc)
    acc (ipat (sexp:list ((sexp:symbol '%ann _) _ (sexp:symbol '-> _)) _) opat . rest)
    -> (parse (list:cons (:tuple (sexp->sexpat ipat) (sexp->sexpat opat)) acc) rest)
    acc exp
    -> (raise (:MacroParseFail (repr (sexp:list exp null-src))))
    )
  (parse (list:nil) pairs)
  )

(define macro/expand
  ;; `exp` is a list starting with the macro's name.
  (:tuple name pats) exp
  -> (let loop ((pats pats))
       (match pats with
         ()
         -> (raise (:MacroFailed name exp))
         ;; try each pattern in turn.
         ((:tuple ipat opat) . rest)
         -> (if (macro/test-one? ipat exp)
                (macro/apply-one ipat opat exp)
                (loop rest))
         )))

