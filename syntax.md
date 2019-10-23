
gaz syntax
----------

    name ::= sexp:symbol
    int ::= sexp:int

    lit ::=
      sexp:int
      ;; eventually vector literals.

    exp ::=
      lit
      name
      (BEGIN exp ...)
      (SET! name exp)
      (IF exp exp exp)
      (LET ((name exp) ...) exp ...)
      (LET name ((name exp) ...) exp ...)
      (APPK name exp ...)
      (name exp ...)

    def ::=
      (DEFINE (name formal ...) exp ...)

    formal ::=
      name <:> type

    type ::=
      i8 i16 .. i256 ;; integers from one to 32 bytes
      (VEC int type) ;; fixed-length vector
      (REF type)     ;; reference
      (QUOTE name)   ;; type variable
      (ARROW type type ...) ;; function signature

