;; -*- mode: irken -*-

;; custom pretty-print with annotation

;; there are still general problems with the annotation output
;;  by the reader.  And this algorithm doesn't do a very good
;;  job - the lazy set!-ing of fsrc doesn't hit correctly.
;;  [I think it's always one atom behind]
;;  all needs to be addressed when src-collapsing happens.

(define (pp-src src exp width)

  ;; will <exp> blow past limit if printed on one line?
  (define (pp-width-check exp limit)
    ;; early exit to avoid crawling huge expressions.
    (let/cc exit
      (let ((sum 0))
        (define (add n)
          (inc! sum n)
          (when (> sum limit)
            (exit #f)))
        (define (S* exps)
          (for-list exp exps
            (S exp)))
        (define S
          (sexp:list ((sexp:symbol '%int) (sexp:int b) (sexp:string digs))) -> (add (+ 2 (string-length digs)))
          (sexp:list ((sexp:symbol '%ann) _ exp)) -> (S exp)
          (sexp:list l)     -> (begin (add (+ 1 (length l))) (S* l))
          (sexp:symbol s)   -> (add (string-length (symbol->string s)))
          (sexp:string s)   -> (add (+ 2 (string-length s))) ;; XXX backslash escapes
          (sexp:char ch)    -> (add (string-length (repr (sexp:char ch))))
          (sexp:bool _)     -> (add 2)
          (sexp:int n)      -> (add (string-length (int->string n)))
          (sexp:undef)      -> (add 2)
          (sexp:vector v)   -> (begin (add (+ 2 (length v))) (S* v))
          ;; we don't expect records/attr/cons/etc in gaz code [yet].
          _                 -> (exit #f)
          )
        (S exp)
        #t
        )))

  (define (format-src path line pos)
    (format
     (ansi green
           (lpad 20 path)
           (lpad 3 (int line))
           "."
           (lpad 3 (int pos)))
            " "
            ))

  (let ((fsrc (format-src "" 0 0)))

    (define set-src!
      (sexp:list ((sexp:symbol 'src) (sexp:string path) (sexp:int line) (sexp:int pos)))
      -> (set! fsrc (format-src path line pos))
      _ -> #u
      )

    (define repr
      (sexp:list ((sexp:symbol '%ann) src exp))
      -> (begin (set-src! src) (repr exp))
      (sexp:list ((sexp:symbol '%int) (sexp:int 10) (sexp:string digits)))
      -> (format digits)
      (sexp:list ((sexp:symbol '%int) (sexp:int 16) (sexp:string digits)))
      -> (format "#x" digits)
      (sexp:list ((sexp:symbol '%int) (sexp:int  8) (sexp:string digits)))
      -> (format "#o" digits)
      (sexp:list ((sexp:symbol '%int) (sexp:int  2) (sexp:string digits)))
      -> (format "#b" digits)
      (sexp:list ((sexp:symbol '%typed) name type))
      -> (format (repr name) ":" (repr type))
      (sexp:list ((sexp:symbol 'quote) x))
      -> (format "'" (repr x))
      (sexp:list l)     -> (format "(" (join repr " " l) ")")
      (sexp:symbol s)   -> (format (sym s))
      (sexp:string s)   -> (repr-string s)
      (sexp:char ch)    -> (repr-char ch)
      (sexp:bool #t)    -> "#t"
      (sexp:bool #f)    -> "#f"
      (sexp:int n)      -> (format (int n))
      (sexp:undef)      -> "#u"
      (sexp:vector v)   -> (format "#(" (join repr " " v) ")")
      (sexp:record fl)  -> (format "{" (join repr-field " " fl) "}")
      (sexp:cons dt c)  -> (format (if (eq? dt 'nil) "" (symbol->string dt)) ":" (sym c))
      (sexp:attr lhs a) -> (format (repr lhs) "." (sym a))
      )

    (define (R* d exps)
      (for-list x exps
        (printf "\n" fsrc (repeat (+ d 1) "  "))
	(R (+ d 1) x)))

    (define (R d exp)
      (if (pp-width-check exp width)
	  (printf (repr exp))
	  (match exp with
	    (sexp:list ())
	    -> (printf "()")
            (sexp:list ((sexp:symbol '%ann) ann exp))
            -> (begin (set-src! ann) (R d exp))
	    (sexp:list (hd . tl))
	    -> (begin (printf "(") (R d hd) (R* d tl) (printf ")"))
            (sexp:vector (hd . tl))
            -> (begin (printf "#(") (R d hd) (R* d tl) (printf ")"))
	    _ -> (printf (repr exp))
            )))

    (set-src! src)
    (printf fsrc)
    (R 0 (sexp (sym '%ann) src exp))
    (printf "\n")
    ))


