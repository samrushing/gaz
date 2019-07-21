;; -*- Mode: Irken -*-

;; the goal here is to begin writing a new language, specifically
;; meant for generating fast, constant-time code for cryptography.

(datatype llt
  (:void)
  (:int int) ;; width in bits.
  (:array int llt)
  (:pointer llt) ;; XXX see if we can avoid this
  (:struct (list llt))
  ;; opaque, float, etc...
  )

(define format-llt
  (llt:void)         -> (format "void")
  (llt:int bits)     -> (format "i" (int bits))
  (llt:array size t) -> (format "[" (int size) " x " (format-llt t) "]")
  (llt:pointer t)    -> (format (format-llt t) "*")
  (llt:struct ts)    -> (format "{" (join format-llt ", " ts) "}")
  )

(datatype llval
  (:ref llt int)     ;; 'register' : %r0, %r1, ...
  (:imm llt int)     ;; "i1 true"
  (:name llt symbol) ;; "i64 %argc"
  ;; (:void) ;; probably needed.
  )

(define llval/type
  (llval:ref t _)  -> t
  (llval:imm t _)  -> t
  (llval:name t _) -> t
  )

(define format-llval
  (llval:ref t n)  -> (format (format-llt t) " %r" (int n))
  (llval:imm t v)  -> (format (format-llt t) " " (int v))
  (llval:name t s) -> (format (format-llt t) " %" (sym s))
  )

(datatype llcmp
  (:eq)  ;; equal
  (:ne)  ;; not equal
  (:ugt) ;; unsigned greater than
  (:uge) ;; unsigned greater or equal
  (:ult) ;; unsigned less than
  (:ule) ;; unsigned less or equal
  (:sgt) ;; signed greater than
  (:sge) ;; signed greater or equal
  (:slt) ;; signed less than
  (:sle) ;; signed less or equal
  )

(define format-llcmp
  (llcmp:eq)  -> "eq"
  (llcmp:ne)  -> "ne"
  (llcmp:ugt) -> "ugt"
  (llcmp:uge) -> "uge"
  (llcmp:ult) -> "ult"
  (llcmp:ule) -> "ule"
  (llcmp:sgt) -> "sgt"
  (llcmp:sge) -> "sge"
  (llcmp:slt) -> "slt"
  (llcmp:sle) -> "sle"
  )

(datatype llop
  ;; arithmetic
  (:add llval llval)
  (:sub llval llval)
  (:mul llval llval)
  (:udiv llval llval)
  (:sdiv llval llval)
  (:urem llval llval)
  (:srem llval llval)
  ;; bitwise
  (:shl llval llval)
  (:lshr llval llval)
  (:ashr llval llval)
  (:and llval llval)
  (:or llval llval)
  (:xor llval llval)
  ;; others
  ;; XXX tail/musttail/fastcc/etc
  (:call llt symbol (list llval)) ;; type, name, args
  (:alloca llt int)               ;; type, count. [XXX align]
  (:load llval)                   ;; pointer
  (:store llval llval)            ;; val, pointer
  (:icmp llcmp llt llval llval)   ;; cond, type, args
  ;; :select
  ;; :getelementptr
  )

;; format an arg without its type.
(define f-arg
  (llval:ref t reg) -> (format "%r" (int reg))
  (llval:imm t val) -> (format (int val))
  (llval:name t s)  -> (format "%" (sym s))
  )

;; strip an outer pointer
(define llt/un*
  (llt:pointer x) -> x
  x -> (raise (:LLVM/ExpectedPointer x))
  )

(define format-llop
  t (llop:add v0 v1)  -> (format "add "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:sub v0 v1)  -> (format "sub "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:mul v0 v1)  -> (format "mul "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:udiv v0 v1) -> (format "udiv " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:sdiv v0 v1) -> (format "sdiv " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:urem v0 v1) -> (format "urem " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:srem v0 v1) -> (format "srem " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:shl v0 v1)  -> (format "shl "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:lshr v0 v1) -> (format "lshr " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:ashr v0 v1) -> (format "ashr " (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:and v0 v1)  -> (format "and "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:or v0 v1)   -> (format "or "   (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:xor v0 v1)  -> (format "xor "  (format-llt t) " " (f-arg v0) ", " (f-arg v1))
  t (llop:alloca t n) -> (format "alloca " (format-llt t) ", i32 " (int n))
  t (llop:load p)     -> (format "load " (format-llt (llt/un* (llval/type p))) ", " (format-llval p))
  t (llop:store v p)  -> (format "store " (format-llval v) ", " (format-llval p))
  t (llop:icmp c t v0 v1)
  ;; XXX assert type of v0/v1 equal?
  -> (format "icmp " (format-llcmp c) " " (format-llt (llval/type v0)) " " (f-arg v0) ", " (f-arg v1))
  t (llop:call t0 name args)
  -> (format "tail call fastcc " (format-llt t) " @" (sym name) "(" (join format-llval ", " args) ")")
  )

(datatype llbb
  ;; insn with result
  (:insn int llt llop llbb) ;; reg type op rest
  ;; void insn
  (:vinsn llop llbb) ;; op rest
  ;; terminators
  (:ret llval)
  (:switch llval symbol (list (:tuple int symbol))) ;; val, default-label, (value label)*
  ;;(:br ...)
  )

(define (format-case t)
  (let ((ft (format-llt t)))
    (define F (:tuple val label) -> (format ft " " (int val) ", label %" (sym label)))
    F))

(define print-llbb
  (llbb:ret v)
  -> (printf "  ret " (format-llval v) "\n")
  (llbb:vinsn op rest)
  -> (begin
       (printf "  " (format-llop (llt:void) op) "\n")
       (print-llbb rest))
  (llbb:insn trg t op rest)
  -> (begin
       (printf "  %r" (int trg) " = " (format-llop t op) "\n")
       (print-llbb rest))
  (llbb:switch val default arms)
  -> (printf "  switch " (format-llval val)
             ", label %" (sym default)
             " [ " (join (format-case (llval/type val)) " " arms) " ] \n")
  )

(datatype llfun
  (:t symbol                      ;; name
      llt                         ;; return type
      (list (:tuple llt symbol))  ;; arg types/names
      (list (:tuple symbol llbb)) ;; (label insn ...) ...
      ))

(define format-arg
  (:tuple t name) -> (format (format-llt t) " %" (sym name))
  )

(define print-llfun
  (llfun:t name rtype argtypes blocks)
  -> (begin
       (printf "define fastcc " (format-llt rtype) " @" (sym name)
               "(" (join format-arg ", " argtypes) ") {\n")
       (for-list label-bb blocks
         (match label-bb with
           (:tuple 'none bb)
           -> (print-llbb bb)
           (:tuple name bb)
           -> (begin
                (printf "\n" (sym name) ":\n")
                (print-llbb bb))))
       (printf "}\n"))
  )

;; --- tiny llvm DSL ---

(defmacro llt
  (llt <i1>)        -> (llt:int 1)
  (llt <i8>)        -> (llt:int 8)
  (llt <i16>)       -> (llt:int 16)
  (llt <i32>)       -> (llt:int 32)
  (llt <i64>)       -> (llt:int 64)
  (llt <i128>)      -> (llt:int 128)
  (llt <void>)      -> (llt:void)
  (llt (<i> n))     -> (llt:int n)
  (llt (<a> n t))   -> (llt:array n (llt t))
  (llt (<*> t))     -> (llt:pointer (llt t))
  (llt (<s> t ...)) -> (llt:struct ((llt t) ...))
  )

(defmacro llval
  (llval (<I> t n)) -> (llval:imm (llt t) n)  ;; immediate
  (llval (<R> t n)) -> (llval:ref (llt t) n)  ;; register
  (llval (t s))     -> (llval:name (llt t) s) ;; name
  )

;; note: (%%constructor 'x 'y) => x:y
(defmacro llop
  (llop name arg ...) -> ((%%constructor llop name) (llval arg) ...)
  )

(defmacro llcmp
  (llcmp <eq>)  -> (llcmp:eq)
  (llcmp <ne>)  -> (llcmp:ne)
  (llcmp <ugt>) -> (llcmp:ugt)
  (llcmp <uge>) -> (llcmp:uge)
  (llcmp <ult>) -> (llcmp:ult)
  (llcmp <ule>) -> (llcmp:ule)
  (llcmp <sgt>) -> (llcmp:sgt)
  (llcmp <sge>) -> (llcmp:sge)
  (llcmp <slt>) -> (llcmp:slt)
  (llcmp <sle>) -> (llcmp:sle)
  )

(defmacro llbb
  (llbb (<ret> v))                       -> (llbb:ret (llval v))
  (llbb (<switch> v def (n lab) ...))    -> (llbb:switch (llval v) def ((:tuple n lab) ...))
  (llbb (r t0 (<call> t1 name arg ...))
        insn ...)                        -> (llbb:insn
                                             r (llt t0)
                                             (llop:call (llt t1) name (list (llval arg) ...))
                                             (llbb insn ...))
  (llbb (r t (<alloca>)) insn ...)       -> (llbb:insn r (llt t) (llop:alloca (llt t) 1) (llbb insn ...))
  (llbb (r t (<alloca> n)) insn ...)     -> (llbb:insn r (llt t) (llop:alloca (llt t) n) (llbb insn ...))
  (llbb (r t (<load> p)) insn ...)       -> (llbb:insn r (llt t) (llop:load (llval p)) (llbb insn ...))
  (llbb (_ (<store> v p)) insn ...)      -> (llbb:vinsn (llop:store (llval v) (llval p)) (llbb insn ...))
  (llbb (r t (<icmp> c v0 v1)) insn ...) -> (llbb:insn
                                             r (llt t)
                                             (llop:icmp (llcmp c)
                                                        (llt t)
                                                        (llval v0)
                                                        (llval v1))
                                             (llbb insn ...))
  (llbb (_ (op arg ...)) insn ...)       -> (llbb:vinsn (llop op arg ...) (llbb insn ...))
  (llbb (r t (op arg ...)) insn ...)     -> (llbb:insn r (llt t) (llop op arg ...) (llbb insn ...))
  )

(defmacro llfun
  (llfun name rtype ((t f) ...) (insn ...) ...)
  -> (llfun:t name (llt rtype)
              ((:tuple (llt t) f) ...)
              (list (llbblabel insn ...) ...)))

;; a list of basic blocks, with optional label at the front
(defmacro llbblabel
  (llbblabel (<quote> label) insn ...) -> (:tuple (quote label) (llbb insn ...))
  (llbblabel insn ...)                 -> (:tuple 'none (llbb insn ...))
  )

;; ok, where to next?  if we stick to CPS/SSA can we avoid blocks altogether?
;;
;; i.e. irken's SSA form and all tail calls.  phi nodes are
;; represented by making calls with arguments.  [see "A Correspondence
;; between Continuation Passing Style and Static Single Assignment
;; Form" by Richard Kelsey].

;; I suppose we should test this out by writing a factorial function by hand.
;; ah, maybe that shows us an issue: conditionals of any kind require blocks.
;; so we can't completely eliminate blocks, but by never branching backward
;; I think that avoids phi.

;; to build: ./types | opt -O3 | clang -v -x ir - -o thing1

(define (t0)
  (print-llfun
   (llfun
    'factcps
    i64 ((i64 'acc) (i64 'n))
    ((0 i1 (icmp eq (i64 'n) (I i64 1)))
     (switch (R i1 0) 'done (0 'again)))
    ('done
     (ret (i64 'acc)))
    ('again
     (1 i64 (mul (i64 'acc) (i64 'n)))
     (2 i64 (sub (i64 'n) (I i64 1)))
     (3 i64 (call i64 'factcps (R i64 1) (R i64 2)))
     (ret (R i64 3))
     )))

  (print-llfun
   (llfun
    'main
    i64 ((i64 'argc) ((* (* i8)) 'argv))
    ((0 i64 (call i64 'factcps (I i64 1) (i64 'argc)))
     (ret (R i64 0)))
    )))

;; ok, now we need to think up to the next language.
;; what CPS lang will convert to this?
;; maybe we even need to start at the other end?
;;

;; ok, let's use the colon syntax for adding type decls
;;   to all binding positions.
;; next question: how much 'type inference' do we need in
;;   order to move from that pre-condition?  Do we need HM?
;;   is there something simpler?
;;
;; just thinking of a simple type checker, the only tricky
;;   part is with literals, since we don't know what kind of
;;   integer they are until we combine them with something.
;;
;; since our target language has no data structures other than
;; T = int | vec(T,n)
;; this should be pretty easy, yes?

;; choices for typing information:
;; A) (define (fact acc:i64 n:i64) ...) [result type is computed]
;; B) (define (fact acc n) ...) : (i64 i64 -> i64)
;;
;; B is more 'traditional' in functional languages, but this would
;;   mean that types in let bindings are different.
;; A is less traditional, but will have consistency in that all
;;   binding positions have type info associated directly.
;;
;; I think A is the best choice for now?
;;
;;
;; -------------------------------------
;; ok, what might the IR look like?  A typed cps I think.
;;

;; what features will this language have?  it should be like C:
;;
;;   no closures
;;   no continuations
;;   no polymorphism
;;   macros? [handy for crypto stuff maybe? what stuff that cannot
;;            be done with inlining would macros allow?]
;;
;; let's start with the high-level language first.
;; so we need a parser and a datatype.  do we go right to CPS
;;   or make that a transform?
;;
;; we could use andrew kennedy's paper as a starting point.
;;

(define (t1)
  (let ((exps (%%sexp
               (define (factcps acc:i64 n:i64)
                 (if (= n 1)
                     acc
                     (factcps (* acc n) (- n 1))))
               (define (thing s:(* i8))
                 (let ((x:i1 0)
                       (y:i8 7))
                   (do-something s x y)))
               )))
    (for-list exp exps
      (pp exp 30)
      )))
