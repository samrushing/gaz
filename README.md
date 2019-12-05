
Gaz, a language for cryptography.
---------------------------------

Gaz is an experimental domain-specific language for cryptography.

Goals
-----

    * small
    * no undefined behavior
    * no signed types
    * no branching (or rather, branching only for fixed-size loops).
    * no memory allocation
    * as much as possible, coddle the constant-timer.
    * minimize assignment/memory
    * promote functional style to ease the task of making formal proofs.
    * output: a C-compatible library for constant-time crypto.

Why?
----

Gaz is written in Irken.  Irken is a high-level functional language -
an unholy hybrid of Scheme and OCaml.  One of Irken's goals is to
provide a framework for scalable servers.  It has an implementation of
h2 and tls-1.3, and needs crypto.  libsodium/nacl provides many of the
needed pieces, but not _all_ of them.  For example, to establish a
session, signing with an x509 cert is necessary, and today most of
those are RSA or EC (like p256) certs.  Eventually, the CA/Browser
folks will allow ed25519 certs and this will all have been a waste of
time.

Irken has been around for about 10 years, and has no users.  In a way,
this is an ideal situation for the language developer.  But, sure, I
wouldn't mind if others appreciated its awesomeness.

A huge barrier to Irken's adoption is its rather poor (atrocious)
error reporting.  Gaz has been a testbed for new approaches to parsing
and macro expansion for irken.  Since it is a much smaller language, I
can iterate quickly on new ideas.  Good progress has been made!

I'm also just interested in cryptography, and I have noticed many
calls for a crypto-specific language, but nothing has emerged that
hits the sweet spot.  Crypto needs a safe, small, restricted language
amenable to formal proof and efficient code generation.

The Gaz Language
----------------

Gaz looks like a simplified scheme, but statically typed.  Currently,
it compiles to LLVM.

The type system:

    * unsigned integers of fixed size: i1, i8, i16, i32, i64, i128, i256...
    * fixed-size vectors/arrays of those integers.
    * references (mutable and constant) to the above.

    T = i1|i8|i16|...
      | (vec <size> T)
      | (ref T)
      | (mut T)

Sample Code
-----------

[Something small here, like xoroshiro or nearly-divisionless]


Compilation
-----------

The stages of Gaz compilation:

    * s-expression parsing of the input files.
    * macro expansion.
    * conversion to the core language ('zexp')
    * conversion to CPS (continuation-passing style).
    * optimization
    * conversion to LLVM (or assembly).

Gaz builds upon a tiny 'core' language:

    * variable-reference
    * sequence
    * let-value
    * let-loop
    * let-continuation
    * set!
    * if
    * goto
    * prim
    * funcall

Macros
------

Gaz uses a macro-by-example system (similar to scheme's `syntax-rules`).
The macros are defined using pattern matching against s-expressions.

The larger Gaz language is defined by the macro transformations in `basis.scm`.

For example, the `*` operation:

    ```scheme
    (defmacro *
      (* x)       -> x
      (* a b ...) -> (%prim * a (* b ...))
      )
    ```

With that macro, the following expression...

    ```scheme
    (* x 7 c)
    ```

...transforms into:

    ```scheme
    (%prim * x (%prim * 7 c))
    ```

A more complex macro...

    ```scheme
    (defmacro while
      (while test body ...)
      -> (let $loop ()
           (when test
             body ...
             (goto $loop))))
     ```

... adds the `while` form.  It translates into a lower-level
construct `let loop`, which in turn uses other macros, like `when`.

[reference "... macros ... their specifications .." here]

LLVM
----

Gaz currently targets the LLVM IR.  This is a great target: it's
typed, it's SSA, and their back end can generate code for many
different targets (and targets with different capabilities like
AVX2/Neon/etc).

That said, it would be nice if Gaz could also output assembly
directly, thereby removing some of the uncertainty around LLVM's
friendliness to constant-time code.  In an ideal world, LLVM will add
features/attributes to accommodate cryptographers.

Direct assembly output would make Gaz more like `qhasm`: it would need
a register allocator, and backends for different architectures.  Gaz's
radically simplified language should make this not too difficult.

CPS vs SSA, letcont
-------------------

Gaz uses CPS as its intermediate representation.  Modern (imperative)
compilers like LLVM use SSA.  Functional compilers often use CPS.  But
CPS and SSA are like two sides of the same coin, mathematical 'duals'
if you will.

The CPS transform used here is based on Andrew Kennedy's excellent
paper "Compiling with Continuations, Continued".

`let` bindings in gaz translate directly into SSA variables.
`letcont` represents a basic block that can be branched to.

`zexp:loop` translates into a CPS `letcont` where both

[wow this is going off the rails]

modular integers
----------------

discuss bearssl/pornin/i31, etc here.

