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
          (sexp:list ((sexp:symbol '%int _) (sexp:int b _) (sexp:string digs _)) _) -> (add (+ 2 (string-length digs)))
          (sexp:list ((sexp:symbol '%ann _) _ exp) _) -> (S exp)
          (sexp:list l _)     -> (begin (add (+ 1 (length l))) (S* l))
          (sexp:symbol s _)   -> (add (string-length (symbol->string s)))
          (sexp:string s _)   -> (add (+ 2 (string-length s))) ;; XXX backslash escapes
          (sexp:char ch _)    -> (add (string-length (repr (sexp:char ch null-src))))
          (sexp:bool _ _)     -> (add 2)
          (sexp:int n _)      -> (add (string-length (int->string n)))
          (sexp:undef _)      -> (add 2)
          (sexp:vector v _)   -> (begin (add (+ 2 (length v))) (S* v))
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
      (sexp:list ((sexp:symbol 'src _) (sexp:string path _) (sexp:int line _) (sexp:int pos _)) _)
      -> (set! fsrc (format-src path line pos))
      _ -> #u
      )

    (define repr
      (sexp:list ((sexp:symbol '%ann _) src exp) _)
      -> (begin (set-src! src) (repr exp))
      (sexp:list ((sexp:symbol '%int _) (sexp:int 10 _) (sexp:string digits _)) _)
      -> (format digits)
      (sexp:list ((sexp:symbol '%int _) (sexp:int 16 _) (sexp:string digits _)) _)
      -> (format "#x" digits)
      (sexp:list ((sexp:symbol '%int _) (sexp:int  8 _) (sexp:string digits _)) _)
      -> (format "#o" digits)
      (sexp:list ((sexp:symbol '%int _) (sexp:int  2 _) (sexp:string digits _)) _)
      -> (format "#b" digits)
      (sexp:list ((sexp:symbol '%typed _) name type) _)
      -> (format (repr name) ":" (repr type))
      (sexp:list ((sexp:symbol 'quote _) x) _)
      -> (format "'" (repr x))
      (sexp:list l _)     -> (format "(" (join repr " " l) ")")
      (sexp:symbol s _)   -> (format (sym s))
      (sexp:string s _)   -> (repr-string s)
      (sexp:char ch _)    -> (repr-char ch)
      (sexp:bool #t _)    -> "#t"
      (sexp:bool #f _)    -> "#f"
      (sexp:int n _)      -> (format (int n))
      (sexp:undef _)      -> "#u"
      (sexp:vector v _)   -> (format "#(" (join repr " " v) ")")
      (sexp:record fl _)  -> (format "{" (join repr-field " " fl) "}")
      (sexp:cons dt c _)  -> (format (if (eq? dt 'nil) "" (symbol->string dt)) ":" (sym c))
      (sexp:attr lhs a _) -> (format (repr lhs) "." (sym a))
      )

    (define (R* d exps)
      (for-list x exps
        (printf "\n" fsrc (repeat (+ d 1) "  "))
	(R (+ d 1) x)))

    (define (R d exp)
      (if (pp-width-check exp width)
	  (printf (repr exp))
	  (match exp with
	    (sexp:list () _)
	    -> (printf "()")
            (sexp:list ((sexp:symbol '%ann _) ann exp) _)
            -> (begin (set-src! ann) (R d exp))
	    (sexp:list (hd . tl) _)
	    -> (begin (printf "(") (R d hd) (R* d tl) (printf ")"))
            (sexp:vector (hd . tl) _)
            -> (begin (printf "#(") (R d hd) (R* d tl) (printf ")"))
	    _ -> (printf (repr exp))
            )))

    (set-src! src)
    (printf fsrc)
    (R 0 (sexp (sym '%ann) src exp))
    (printf "\n")
    ))


