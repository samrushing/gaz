;; -*- Mode: Irken -*-

;; parser combinators.
;; references:
;; https://www.youtube.com/watch?v=RDalzi7mhdY "Understanding Parser Combinators"
;; https://fsharpforfunandprofit.com/posts/understanding-parser-combinators/
;; https://github.com/inhabitedtype/angstrom/
;;
;; Note: monad/currying weirdness makes some of the 'pure' monadic stuff
;;   not work.  I cribbed `lift2` from angstrom for this reason.
;;
;; this is a version of parsec modified to parse and keep src annotations,
;;   for both :ok and :no results.
;;

;; annotation: source-code location
(typealias src {path=string line=int pos=int})

(datatype result
  (:ok src 'a 'b)       ;; result, rest-of-input
  (:no src sexp string) ;; label, error string
  (:fail src sexp string) ;; label, error string
  )

(define (parser/make fun label)
  (define (debug x)
    (printf "app: " (repr label) "\n")
    (printf "     " (join repr " " (map remove-annotations x)) "\n")
    (fun x))
  {fun=fun label=label}
  ;;{fun=debug label=label}
  )

(defmacro parser
  (parser fun)       -> (parser/make fun (sexp:undef))
  (parser fun label) -> (parser/make fun label)
  )

(define (pc/set-label p label)
  (set! p.label label)
  p)

;; note - F# infix semantics:
;; x OP y OP z => (OP x (OP y z))

(define (andThen parser1 parser2)
  (let ((label (sexp (sym 'and) parser1.label parser2.label)))
    (parser/make
     (lambda (input)
       (match (parser1.fun input) with
         (result:ok src1 v1 rest)
         -> (match (parser2.fun rest) with
              ;; note: our src annotation does not do extents, only 'starts at',
              ;;   so combining with andThen means we have to choose src1.  if we
              ;;   did extents, this would be the logical place to combine them.
              (result:ok src2 v2 rest)
              -> (result:ok src1 (:tuple v1 v2) rest)
              (result:no src _ err)
              -> (result:no src parser2.label err)
              (result:fail src lab err)
              -> (result:fail src lab err)
              )
         (result:no src _ err)
         -> (result:no src parser1.label err)
         (result:fail src lab err)
         -> (result:fail src lab err)
         ))
     label)))

(define (orElse parser1 parser2)
  (let ((label (sexp (sym 'or) parser1.label parser2.label)))
    (define (inner input)
      (match (parser1.fun input) with
        (result:no _ _ _)
        -> (parser2.fun input)
        (result:fail src lab err)
        -> (result:fail src lab err)
        ;; note: we can return the success result directly,
        ;;  because it has the same type.
        success
        -> success
        ))
    (parser/make inner label)))

(define choice*
  (a b)     -> (orElse a b)
  (hd . tl) -> (orElse hd (choice* tl))
  _         -> (raise (:BadChoice))
  )

(defmacro choice
  (choice a ...) -> (choice* (list a ...))
  )

(define (mapP f parser prefix)
  (let ((label (sexp (sym prefix) parser.label)))
    (parser/make
     (lambda (input)
       (match (parser.fun input) with
         (result:ok src v rest)
         -> (result:ok src (f v) rest)
         (result:no src _ err)
         -> (result:no src label err)
         (result:fail src lab err)
         -> (result:fail src lab err)
         ))
     label
     )))

(define (lift2 f prefix)
  (lambda (p1 p2)
    (let ((label (sexp (sym prefix) p1.label p2.label)))
      (parser/make
       (lambda (input)
         (match (p1.fun input) with
           (result:ok src1 v1 rest1)
           -> (match (p2.fun rest1) with
                ;; again: this is where we might merge extents.
                (result:ok src2 v2 rest2)
                -> (result:ok src1 (f v1 v2) rest2)
                (result:no src _ err)
                -> (result:no src label err)
                (result:fail src _ err)
                -> (result:fail src label err)
                )
           (result:no src _ err)
           -> (result:no src label err)
           (result:fail src lab err)
           -> (result:fail src lab err)
           ))
       label
       ))))

;; XXX find a way to actually cons the labels...
(define consP (lift2 list:cons 'cons))

(define null-src {path="null" line=-1 pos=-1})

;; XXX might the src be a parameter here?
(define (returnP x label)
  (parser/make
   (lambda (input)
     (result:ok null-src x input))
   label))

(define (sequence* parserList)
  (match parserList with
    ()        -> (returnP (list:nil) (sexp:list ()))
    (hd . tl) -> (consP hd (sequence* tl))
    ))

(defmacro sequence
  (sequence x ...) -> (sequence* (list x ...))
  )

;; helper for star & plus
(define (zero-or-more parser input)
  (let loop ((acc (list:nil))
             (srcs (list null-src))
             (r (parser.fun input))
             (input input))
    (match r with
      (result:no _ _ _)
      -> (:good (reverse acc) (reverse srcs) input)
      (result:fail src lab err)
      -> (:bad src lab err)
      (result:ok src val rest)
      -> (loop (list:cons val acc)
               (list:cons src srcs)
               (parser.fun rest)
               rest))))

(define (star parser)
  (define (inner input)
    (match (zero-or-more parser input) with
      (:good v srcs rest)
      -> (result:ok (first srcs) v rest)
      (:bad src lab err)
      -> (result:fail src lab err)
      ))
  (parser/make inner (sexp (sym 'star) parser.label)))

(define (plus parser)
  (let ((label (sexp (sym 'plus) parser.label)))
    (define (inner input)
      (match (parser.fun input) with
        (result:no src _ err)
        -> (result:no src label err)
        (result:fail src lab err)
        -> (result:fail src lab err)
        (result:ok src v1 rest)
        -> (match (zero-or-more parser rest) with
             (:good others srcs rest)
             -> (result:ok src (list:cons v1 others) rest)
             (:bad src lab err)
             -> (result:fail src lab err)
             )))
    (parser/make inner label)))

(define (opt parser)
  (orElse
   (mapP maybe:yes parser 'opt)
   (returnP (maybe:no) (sexp:symbol 'null))))

(define (*>> p1 p2)
   (mapP (lambda (:tuple a b) a) (andThen p1 p2) '*>>))

(define (>>* p1 p2)
  (mapP (lambda (:tuple a b) b) (andThen p1 p2) '>>*))

(define (between p1 p2 p3)
  (pc/set-label
   (>>* p1 (*>> p2 p3))
   (sexp (sym 'between) p1.label p2.label p3.label)))

(define (sepBy1 p sep)
  (pc/set-label
   (mapP
    (lambda (:tuple p plist) (list:cons p plist))
    (andThen p (star (>>* sep p)))
    'sepBy1)
   (sexp (sym 'sepBy1) p.label sep.label)))

(define (sepBy p sep)
  (pc/set-label
   (orElse
    (sepBy1 p sep)
    (returnP (list:nil)))
   (sexp (sym 'sepBy) p.label sep.label)))

;; needed for recursive parsers.
(define (fix f)
  (define p (lazy (f r)))
  (define r
    (parser/make
     (lambda (input)
       (let ((p0 (force p)))
         (p0.fun input)))
     (sexp:symbol 'lazy)))
  r)

;; converts soft fail to hard fail.
(define (must p)
  (define (inner input)
    (match (p.fun input) with
      (result:no src lab err)
      -> (result:fail src lab err)
      ;; (result:fail src lab err)
      ;; -> (result:fail src lab err)
      ;; (result:ok src val rest)
      ;; -> (result:ok src val rest)
      otherwise
      -> otherwise
      ))
  (parser/make inner (sexp (sym 'must) p.label))
  )
