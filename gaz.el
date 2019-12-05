;; -*- Mode: Emacs-Lisp -*-

(require 'scheme)

;; decorate name:type properly.
(defun gaz-font-lock-type (limit)
  (when (search-forward ":" limit t)
    (let ((beg (match-end 0)))
      (ignore-errors
        (forward-sexp 1)
        (set-match-data (list beg (point)))
        (point)))))

(defun gaz-font-lock-var (limit)
  (when (search-forward ":" limit t)
    (let ((beg (match-beginning 0)))
      (save-excursion
        (backward-sexp 1)
        (set-match-data (list (point) beg))
        beg))))

;; I think I need to modify the syntax table entry for ':'
(defconst gaz-font-lock-keywords
  (eval-when-compile
    (list
     (cons
      (concat
       ;; Note the "(", these only trigger in operator position.
       "(" (regexp-opt
	    '("begin" "if" "let" "define" "declare" "set!" "appk" "goto" "prim"
              "defmacro" "define" "define-constant" "define-mutable" "for") t)
       "\\>") 1)
     ;; named let
     '("(let\\s-+\\(\\sw+\\)" (1 font-lock-function-name-face))
     ;; functions
     '("(define\\s-+(?\\([^ :\t\n)]+\\)" . (1 font-lock-function-name-face))
     '("(declare\\s-+(?\\([^ :\t\n)]+\\)" . (1 font-lock-function-name-face))
     '("(defmacro\\s-+(?\\([^ :\t\n)]+\\)" . (1 font-lock-function-name-face))
     ;; builtins
     '("(\\(%[^ :\t\n)]+\\)" . font-lock-builtin-face)
     ;; name:type
     '(gaz-font-lock-var  (0 font-lock-variable-name-face))
     '(gaz-font-lock-type (0 font-lock-type-face))
     '("->" . font-lock-function-name-face)
      ))
  "Gaudy expressions to highlight in Scheme modes.")

;;;###autoload
(define-derived-mode gaz-mode scheme-mode "Gaz"
  "Major mode for editing Gaz code."
  :syntax-table nil
  (setq major-mode 'gaz-mode
	mode-name "Gaz")
  (setq font-lock-defaults
       '((gaz-font-lock-keywords))
       ;; nil t (("+-*/.<>=!?$%_&~^:" . "w") (?#. "w 14"))
       ;; beginning-of-defun
       ;; (font-lock-mark-block-function . mark-defun)
       ;; (font-lock-syntactic-face-function
       ;; 	. scheme-font-lock-syntactic-face-function)
         ;; (parse-sexp-lookup-properties . t)
         ;; (font-lock-extra-managed-props syntax-table)))
       )
  )

(put 'letcont 'scheme-indent-function 1)
(put 'for 'scheme-indent-function 1)

(provide 'gaz)
