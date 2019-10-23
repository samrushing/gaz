;; -*- Mode: Irken -*-

(require "lib/basis.scm")
(require "lib/cmap.scm")
(require "lib/partial.scm")
(require "./read.scm")
(require "./parsec.scm")
(require "./types.scm")
(require "./lazy.scm")
(require "./zexp.scm")
(require "./parse.scm")
(require "./alpha.scm")
(require "./cps.scm")
(require "./rewrite.scm")
(require "./solve.scm")
;;(require "./cps2llvm.scm")

;; ----- testing -----

(define (parse-zfun s)
  (let ((p (zp-defn))
        (exp0 (read2 "test" (string-reader s) #t)))
    (pp0 (first exp0) 80 0 "")
    (match (p.fun exp0) with
      (result:no src label err)
      -> (begin
           (printf "unable to parser while reading " (repr label) "\n")
           (printf "err = " err "\n")
           (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
           (raise (:ParseFail)))
      (result:fail src label err)
      -> (begin
           (printf (bold "parse fail") " while reading " (repr label) "\n")
           (printf "err = " err "\n")
           (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
           (raise (:ParseFail)))
      (result:ok src fun rest) ;; note: ignoring `rest`
      -> (begin
           (printf "result:\n")
           (dump-azfun fun) (printf "\n")
           (printf " at " (string src.path) ":" (int src.line) ":" (int src.pos) "\n")
           (:tuple src fun)
           )
      )))

;; XXX YOU ARE HERE
;; lotta stuff unfinished all over the place, but the next logical
;;  step to the 'end' is to invoke cps2llvm on this. then we need to:
;;
;;  X * parse to zfun
;;  * cps2llvm
;;    needs to be taught about types.
;;  * do 'something' with src information
;;     * eventually fix/test parse errors
;;  * add type checking
;;  * propagate type info all the way down to llvm
;;  * MBE
;;
;;  [eventually]
;;  * revisit the awfulness that is the parser AGAIN.
;;    I think it might be possible to do something like parsec, but simplified
;;    and more s-expression friendly?

(define (tcps s)
  (match (parse-zfun s) with
    (:tuple src fun)
    -> (let ((fun0 (alpha fun)))
         (match fun0 with
           (zfun:t name formals body)
           -> (let ((cps0 (zexp->cps body))
                    (cps1 (rewrite-cps cps0))
                    )
                (printf "\ncps0:\n")
                (dump-cps 0 cps0)
                (printf "\ncps1:\n")
                (dump-cps 0 cps1)
                (solve (alist:entry 'halt (list (new-tvar)) (alist:nil)) cps1)
                (dump-cps 0 cps1)
;;              (cpsfun->llvm name args cps1)
                )
           )
         )
    ))

(tcps "
 (define (main argc : i64)
   (let loop ((acc:i64 1)
              (n:i64 argc))
     (if (= n 1)
         acc
         (appk loop (* acc n) (- n 1)))))"
      )

;; (tcps "
;;  (define (main)
;;    (let ((x:i64 0)
;;          (y:i64 1))
;;      (+ x y)))"
;;       )

;; (tcps "
;;  (define (main argc:i64)
;;    (if 1 3 4)
;;    )")

;; (tcps "
;; (define (main)
;;   (let ((z:i32 34)
;;         (y:i32 19))
;;     (* (+ 22 y)
;;        (* z
;;           (+ z
;;              (- y 11))))))")

;; test beta-cont
;; (tcps "
;;  (define (main)
;;    (let ((x:i64 19))
;;      (+ x 34)))"
;;       )

;; test loop in non-tail position
;; (tcps "
;;  (define (main)
;;    (+ (let loop ((n:i32 5))
;;         (if (= n 0)
;;            99
;;            (appk loop (- n 1))))
;;        1))"
;;       )
