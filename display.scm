;; -*- Mode: Irken -*-

;; XXX rename autodisplay?

(define (build-datatype-table)
  (let ((dts (fetch-metadata 'datatypes))
        (table (alist:nil)))

    (define (build-arms arms)
      (define build-args
        acc ((sexp:list type _) . tl) -> (build-args (list:cons type acc) tl)
        acc _                       -> (reverse acc)
        )
      (define B
        acc ((sexp:list ((sexp:symbol name _) (sexp:int tag _) (sexp:list args _)) _) . tl)
        -> (B (alist:entry tag (:tuple name (build-args '() args)) acc) tl)
        acc _
        -> acc
        )
      (B (alist:nil) arms)
      )

    (for-list dt dts
      (match dt with
        (sexp:list ((sexp:symbol name _) (sexp:list arms _)) _)
        -> (alist/push table name (build-arms arms))
        _
        -> (impossible)
        ))
    table
    ))

(define ob->dtarm
  (let ((table (build-datatype-table)))
    (lambda (dt)
      (match (alist/lookup table dt) with
        (maybe:yes arms)
        -> (lambda (ob)
             (let (((payload len tag) (~~get-payload-len-tag ob)))
               (match (alist/lookup arms (- (>> tag 2) 10)) with
                 (maybe:yes (:tuple name type))
                 -> name
                 (maybe:no)
                 -> '???
                 )))
        (maybe:no)
        -> (raise (:KeyError dt))
        ))))

