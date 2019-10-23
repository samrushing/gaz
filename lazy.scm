;; -*- Mode: Irken -*-

;; lazy evaluation

(datatype lazy*
  (:delayed (-> 'a))
  (:value 'a)
  )

;; i.e. (ref (lazy 'a))
(typealias lazy {val=(lazy* 'a)})

(define (lazy/make thunk)
  {val=(lazy*:delayed thunk)}
  )

;; thunkify an expression
(defmacro lazy
  (lazy exp)
  -> (lazy/make (lambda () exp))
  )

(define (force ob)
  (match ob.val with
    (lazy*:value v)
    -> v
    (lazy*:delayed f)
    -> (let ((v (f)))
         (set! ob.val (lazy*:value v))
         v)
    ))

;; lazy streams

(datatype stream
  (:nil)
  ;;(:cell 'a (lazy (stream 'a)))
  (:cell 'a {val=(lazy* (stream 'a))})
  )

(define (stream/take n s)
  (define T
    acc 0 _                   -> (reverse acc)
    acc n (stream:nil)        -> (reverse acc)
    acc n (stream:cell hd tl) -> (T (list:cons hd acc) (- n 1) (force tl)))
  (T (list:nil) n s)
  )

(define (gen->stream gen)
  (match (gen) with
    (maybe:yes val) -> (stream:cell val (lazy (gen->stream gen)))
    (maybe:no)      -> (stream:nil)
    ))

