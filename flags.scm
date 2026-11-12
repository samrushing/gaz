;; -*- Mode: Irken -*-

;; global compiler flags, and macros for conditional output.
;;
;;   (verbose ...)  -v : show the program after each pass.
;;   (trace ...)    -d : trace the type solvers, the rewriter and the evaluator.
;;
;; with neither flag, a successful compile prints nothing.

(define gaz-flags {verbose=#f trace=#f})

(defmacro verbose
  (verbose body ...) -> (when gaz-flags.verbose body ...)
  )

(defmacro trace
  (trace body ...) -> (when gaz-flags.trace body ...)
  )
