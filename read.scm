;; -*- Mode: Irken -*-

;; this is a new version of the lisp reader that includes source
;;  annotations. [from an in-progress modification to irken]

;; modifying to avoid using irken ints.

(define (gaz-read path read-char annotate?)

  (let ((char #\eof) ;; one-character buffer
	(line 1)
	(pos -1)
        (spath (sexp:string path null-src))
        (%ann (sexp:symbol '%ann null-src))
        (src (sexp:symbol 'src null-src))
        )

    (defmacro ERR
      (ERR ob ...)
      -> (raise (:ReadError path line pos (format ob ...)))
      )

    (define (peek)
      char)

    (define (next)
      (let ((result char))
	(if (eq? result #\newline)
	    (begin (inc! line)
		   (set! pos 0))
	    (inc! pos))
	(set! char (read-char))
	result))

    (define (skip-peek)
      (next)
      (peek)
      )

    (define skip-comment
      #\return  -> #u
      #\newline -> #u
      _         -> (skip-comment (skip-peek))
      )

    (define (skip-whitespace)
      (let loop ((ch (peek)))
	(cond ((eq? ch #\eof) #u)
	      ((eq? ch #\;) (skip-comment (skip-peek)) (loop (peek)))
	      ((whitespace? ch) (loop (skip-peek)))
	      (else #u))))

    ;; very tricky, using a state machine
    (define (read-atom)
      (let ((state 0)
	    (dot-count 0)
	    (ch #\0))
	(let loop ((result '()))
	  (set! ch (peek))
	  (if (eq? ch #\.)
	      (set! dot-count (+ dot-count 1)))
	  (set! state
		(match state with
		  0 -> (cond ((eq? ch #\eof) 4)
			     ((eq? ch #\-) 1)
			     ((digit? ch) 2)
			     ((delim? ch) 7)
			     (else 3))
		  1 -> (cond ((eq? ch #\eof) 5)
			     ((delim? ch) 5)
			     ((digit? ch) 2)
			     (else 3))
		  2 -> (cond ((eq? ch #\eof) 6)
			     ((delim? ch) 6)
			     ((digit? ch) 2)
			     (else 3))
		  3 -> (cond ((eq? ch #\eof) 5)
			     ((delim? ch) 5)
			     (else 3))
		  _ -> (impossible)))
	  (cond ((< state 4) (loop (list:cons (next) result))) ;; non-final
		((= state 4) (ERR "unexpected end-of-file" path)) ;; error final
		(else ;; all other finals: 5,6,7
		 ;; single-character - for #\A
		 (if (= state 7) (set! result (list:cons (next) result)))
		 (:atom (list->string (reverse result)) ;; result string
			(= state 6)			;; number?
			(length result)			;; #chars
			dot-count))))))			;; #dots

    (define (dotted-symbol s n)
      ;; handle dots in a symbol
      ;; as a special case, allow all-dots symbols (like '...) through unscathed
      (if (= n (string-length s))
	  (sexp:symbol (string->symbol s) null-src)
	  (let loop ((parts (reverse (string-split s #\.))))
	    ;; a.b.c => (get (get a b) c)
	    (match parts with
	      ;; c b a
	      (base)        -> (sexp:symbol (string->symbol base) null-src)
	      (attr . rest) -> (sexp:attr (loop rest) (string->symbol attr) null-src)
	      ()            -> (impossible)
	      ))))

    (define (read-symbol)
      (match (read-atom) with
	(:atom sym #t _ _) -> (ERR "expected symbol" (string sym))
	(:atom sym #f _ 0) -> (string->symbol sym)
	(:atom sym #f _ _) -> (ERR "no dots allowed in constructor names: " (string sym))
	))

    (define (read1)
      (let ((ch (peek)))
	(match ch with
	  #\eof -> (ERR "unexpected end of file")
	  #\(   -> (sexp:list (read-list) null-src)
	  #\{   -> (read-record)
	  #\"   -> (read-string)
	  #\'   -> (begin (next) (sexp (sexp:symbol 'quote null-src) (read)))
	  #\,   -> (begin (next) (sexp (sexp:symbol 'comma null-src) (read)))
          #\!   -> (begin (next) (sexp (sexp:symbol 'bang null-src) (read)))
	  #\:   -> (begin (next) (sexp:cons 'nil (read-symbol) null-src))
	  #\#   -> (begin
		     (next)
		     (set! ch (peek))
		     (match ch with
		       #\\ -> (begin
				(next) ;; skip backslash
				(match (read-atom) with
				  (:atom atom _ 1 _)      -> (sexp:char (string-ref atom 0) null-src)
				  (:atom "newline" _ _ _) -> (sexp:char #\newline null-src)
				  (:atom "space" _ _ _)   -> (sexp:char #\space null-src)
				  (:atom "return" _ _ _)  -> (sexp:char #\return null-src)
				  (:atom "tab" _ _ _)     -> (sexp:char #\tab null-src)
				  (:atom "eof" _ _ _)     -> (sexp:char #\eof null-src)
				  (:atom "nul" _ _ _)     -> (sexp:char #\nul null-src)
				  (:atom name _ _ _)      -> (ERR "bad character constant: " name)
				   ))
		       ;; Bb
		       #\X -> (begin (next) (read-integer-literal 16))
		       #\x -> (begin (next) (read-integer-literal 16))
		       #\O -> (begin (next) (read-integer-literal 8))
		       #\o -> (begin (next) (read-integer-literal 8))
                       #\B -> (begin (next) (read-integer-literal 2))
                       #\b -> (begin (next) (read-integer-literal 2))
		       #\T -> (begin (next) (sexp:bool #t null-src))
		       #\t -> (begin (next) (sexp:bool #t null-src))
		       #\F -> (begin (next) (sexp:bool #f null-src))
		       #\f -> (begin (next) (sexp:bool #f null-src))
		       #\U -> (begin (next) (sexp:undef null-src))
		       #\u -> (begin (next) (sexp:undef null-src))
		       #\( -> (sexp:vector (read-list) null-src)
		       x   -> (ERR "syntax error: " (char x))
		       ))
	  #\)   -> (ERR "unexpected close-paren")
	  _     -> (match (read-atom) with
                     ;; XXX gaz: need to handle negative integers!
		     (:atom chars #t n _) -> (sexp (sym '%int) (int 10) (string chars))
		     (:atom chars #f _ 0) -> (sexp:symbol (string->symbol chars) null-src)
		     (:atom chars #f _ n) -> (dotted-symbol chars n)
		     )
	  )
	)
      )

    (define (read-postfix)
      (let ((result (read1)))
	(skip-whitespace)
	(let loop ((ch (peek)))
	  (match ch with
            ;; ------ postfix/infix extensions -----
	    ;; array-reference syntax
	    #\[ -> (let ((index (read-array-index)))
		     ;; primops take a parameter---------V
		     (set! result (sexp (sexp:symbol '%array-ref null-src) (sexp:bool #f null-src) result index))
                     (skip-whitespace)
                     (loop (peek)))
	    ;; infix colon syntax
	    #\: -> (begin
		     (next)
		     (match result (read) with
                       ;; NOTE: with annotation turned on, these cases are NOT caught.
                       ;;   which is probably fine, since if you are using annotation
                       ;;   you're probably not the Irken compiler.
                       ;;
                       ;; normal constructor syntax
		       (sexp:symbol dt _) (sexp:symbol alt _) -> (sexp:cons dt alt null-src)
                       ;; object/method syntax (ob::add arg0 ...)
		       ;; not forcing (sexp:symbol) on <ob> might allow 'builtin method calls'...
		       ;;  ob (sexp:cons 'nil method) -> (sexp:attr (sexp:attr ob 'o) method)
                       ob (sexp:cons 'nil method _)
                       -> (sexp (sexp:symbol '%%obref null-src) ob (sexp:symbol method null-src))
                       ;; XXX note: maybe change to an %ann-otation.
		       ;; object : type syntax
		       ob type -> (sexp (maybe-annotate (sexp:symbol '%typed null-src))
                                        (maybe-annotate ob)
                                        type)
		       ;;ob type -> (sexp (sexp:symbol '%typed) ob type)
                       ))
	    _   -> result
	    ))))

    (define (maybe-annotate exp)
      (if annotate?
          (sexp %ann (sexp src spath (int line) (int pos)) exp)
          exp))

    (define (read-array-index)
      (next) ;; skip open-left-bracket
      (let ((exp (read)))
	(skip-whitespace)
	(if (eq? (peek) #\])
	    (begin (next) exp)
	    (ERR "expected closing ]/} character"))))

    (define (read-hex-digit ch)
      (match (alist/lookup hex-map ch) with
	(maybe:no) -> (ERR "bad hex digit: " (char ch))
	(maybe:yes num) -> num))

    (define (read-hex-code)
      (let ((n0 (read-hex-digit (next)))
	    (n1 (read-hex-digit (next))))
	(ascii->char (+ (<< n0 4) n1))))

    (define (read-string)
      (next) ;; throw away the opening quote
      (let loop ((ch (peek))
		 (result '()))
	(match ch with
	  #\" -> (begin
		   (next) ;; throw away the close-quote
		   (sexp:string (list->string (reverse result)) null-src))
	  #\\ -> (begin
		   ;; ignore this backslash, read the next char
		   (next)
		   (set! ch (next))
		   (match ch with
		     #\x -> (let ((sch (read-hex-code))) (loop (peek) (list:cons sch result)))
		     #\X -> (let ((sch (read-hex-code))) (loop (peek) (list:cons sch result)))
		     #\r -> (loop (peek) (list:cons #\return result))
		     #\n -> (loop (peek) (list:cons #\newline result))
		     #\t -> (loop (peek) (list:cons #\tab result))
		     #\" -> (loop (peek) (list:cons #\" result))
		     #\\ -> (loop (peek) (list:cons #\\ result))
		     _   -> (ERR "bad backslash escape in string: " (char ch))
		     ))
	  _   -> (loop (skip-peek) (list:cons ch result))
	  )))

    (define (read-list)
      (next) ;; throw away the open paren
      (let loop ((result '()))
	(skip-whitespace)
        (cond ((eq? (peek) #\))
               (next) ;; throw away the close paren
               (reverse result))
              (else
               (loop (list:cons (read) result))))))

    (define (read-record)
      ;; { label=value label=value ...}
      (next)
      (let loop ((result '()))
	(skip-whitespace)
	(let ((p (peek)))
	  (if (eq? p #\})
	      (begin (next) (sexp:record (reverse result) null-src))
	      (let ((name (read-name)))
		(cond ((eq? name '...)
		       (loop (list:cons (field:t name (sexp:bool #f null-src) null-src) result)))
		      (else
		       (skip-whitespace)
		       (if (not (eq? (peek) #\=))
			   (ERR "expected '=' in record literal: " (char (peek)))
			   (begin
			     (next)
			     (let ((val (read)))
			       (loop (list:cons (field:t name val null-src) result))))))))
	      ))))

    (define (read-name)
      (let loop ((result '())
		 (ch (peek))
		 (dots #f))
	(cond ((or (field? ch) (eq? ch #\.))
	       (loop (list:cons ch result) (skip-peek) #f))
	      (else
	       (string->symbol (list->string (reverse result)))))))

    ;; ----- integer literals -----

    (define hex-digit? (char-class (string->list "0123456789ABCDEFabcdef")))
    (define oct-digit? (char-class (string->list "01234567")))
    (define bin-digit? (char-class (string->list "01")))

    (define (all-int-class? base chars)
      (all?
       (match base with
         16 -> hex-digit?
         8  -> oct-digit?
         2  -> bin-digit?
         _  -> (impossible)
         )
       (string->list chars)))

    ;; XXX gaz: should throw an error with #\-
    (define (read-integer-literal base)
      (match (read-atom) with
        (:atom chars dec? n 0)
        -> (if (all-int-class? base chars)
               (sexp (sym '%int) (int base) (string chars))
               (ERR "unexpected char reading base " (int base)
                    " literal:" (string chars)))
        (:atom chars _ _ _)
        -> (ERR "unexpected char reading base " (int base)
                " literal:" (string chars))
        ))

    ;; ----------

    (define (read)
      (skip-whitespace)
      (let ((line0 line)
            (pos0 pos)
            (result (read-postfix)))
        (if annotate?
            (sexp %ann (sexp src spath (int line0) (int pos0)) result)
            result)))

    (define (read-all acc)
      (if (eq? (peek) #\eof)
          (reverse acc)
          (read-all (list:cons (read) acc))))

    (next)
    (read-all '())
    ))

(define (remove-annotations exp)
  (define RA
    (sexp:list ((sexp:symbol '%ann _) _ x) _) -> (RA x)
    (sexp:list forms _)                     -> (sexp:list (map RA forms) null-src)
    (sexp:vector vs _)                      -> (sexp:vector (map RA vs) null-src)
    (sexp:attr e s _)                       -> (sexp:attr (RA e) s null-src)
    (sexp:record lf _)                      -> (sexp:record (map RAf lf) null-src)
    other                                 -> other
    )
  (define RAf (field:t name e _) -> (field:t name (RA e) null-src))
  (RA exp)
  )

;; ---- modified pprint ----

(define (pp0 exp width depth prefix)
  (define (recur d exp)
    (let ((size (pp-size exp)))
      (if (< size width)
	  (printf (repr exp))
	  (match exp with
	    (sexp:list () _)
	    -> (printf "()")
	    (sexp:list (hd . tl) _)
	    -> (begin (printf "(")
		      (recur d hd)
		      (for-each
		       (lambda (x)
			 (newline)
                         (printf prefix)
			 (indent (+ d 1))
			 (recur (+ d 1) x)) tl)
		      (printf ")"))
	    ;; XXX complete for vector & record.
	    _ -> (printf (repr exp))))))
  (printf prefix)
  (recur depth exp)
  (print-string "\n")
  )

