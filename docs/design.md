# Gaz: design notes

*November 2026.  Gaz was written between July 2019 and January 2020
and then sat for nearly seven years.  This document records what exists,
what was learned on picking it back up, and where it should go next.
Sections marked **(proposed)** describe things that are not implemented.*

## Summary

Gaz is a very small, statically typed language for writing cryptographic
primitives, with a Scheme-like syntax.  The compiler is about 4,900 lines
of Irken.  Today it has:

- a macro layer that defines most of the surface language,
- a ten-form core language with type inference,
- a CPS intermediate form with a small optimizer,
- an LLVM IR backend, and
- an evaluator for the CPS form, which serves as a reference semantics.

It compiles and runs SHA-256, Keccak-f, ChaCha20, an AES S-box generator
and the start of a BearSSL-style bignum layer (`tests/`).

Three things stand between that and a language one could write real
elliptic-curve or lattice code in.  In the order they should be done:

1. **A backend we control.**  LLVM gives no constant-time guarantee.
2. **Carry and widening-multiply primitives, and secrecy labels** on
   types, so the compiler can refuse code that branches or indexes on a
   secret.
3. **Vector sizes as type-level variables**, finishing the `itype:dyn`
   experiment.

## Goals

From the original README, still the right list:

- small
- no undefined behavior
- no branching on data, other than fixed loops
- no memory allocation
- minimal assignment; a functional style, to make proofs easier
- output: a C-callable library of constant-time code

One goal has changed.  "No signed types" came from the unpredictability
of signed integers in C.  It stays, but in a more precise form: integers
are bit patterns with wraparound arithmetic, and signedness belongs to
the *operation* (see [Signedness](#signedness-proposed)).

Non-goals: general-purpose programming, heap data, closures, recursion,
separate compilation, and being trusted by anyone else for production
crypto.  That last needs formal verification, which is Jasmin's
territory.  Gaz is for understanding and controlling one's own crypto,
and for being small enough to read in an afternoon.

## The language today

### Types

    T = i1 | i8 | i16 | i31 | i32 | i64 | i128 | i256
      | (vec <size> T)
      | (ref T)          ; read-only reference
      | (mut T)          ; mutable reference
      | none

Integers are unsigned and wrap.  A `let`-bound variable is immutable;
anything assignable is a `(mut T)`, created with `(alloca)` or
`define-mutable`.  A variable of reference type is dereferenced
automatically when used as a value (the `ref-ref` pass).

`x[i]` is reader syntax for a vector reference, and `name:type` for a
typed name.

Internally a vector type carries a third, hidden parameter that records
whether it is used as an LLVM *vector* (arithmetic on the whole thing)
or an LLVM *array* (indexed through a pointer).  It is inferred, and it
exists only because of LLVM.

### Core forms

Everything reduces to ten forms (`zexp.scm`):

| Form | Meaning |
| --- | --- |
| literal | integer or vector literal |
| variable reference | |
| `%prim` | a primitive operation: `+`, `xor`, `<<<`, `%vref`, ... |
| sequence | |
| let | bind one immutable value |
| if | two-way branch |
| call | call a top-level function |
| loop | named `let`: a block with parameters |
| letcont | a named continuation: a block that can be jumped to |
| appk / `goto` | jump to a loop or continuation, with arguments |

There are no nested functions and no closures.  Loops and local exits
are both "goto with arguments".

### Macros

The surface language is built from the core by macro-by-example
(`macros.scm`, with the definitions in `gaz-basis.scm`): `define`,
n-ary `+` and `xor`, `for`, `while`, `cond`, `when`, `set!`, `inc!`,
and so on.  User programs define their own the same way; the ChaCha20
quarter-round is a macro.

### Pipeline

| Stage | File | |
| --- | --- | --- |
| read | `read.scm` | s-expressions, with a source location attached to each |
| expand | `macros.scm` | macro expansion |
| parse | `parse.scm` | s-expression to core (`zexp`) |
| rename | `alpha.scm` | every binding gets a unique name |
| ref-ref | `zexp.scm` | insert dereferences |
| solve | `solve.scm` | type inference by unification, on the core |
| CPS | `cps.scm` | after Kennedy, *Compiling with Continuations, Continued* |
| solve | `solve.scm` | type inference again, on the CPS |
| rewrite | `rewrite.scm` | dead code, eta and beta reduction of continuations |
| emit | `llvm.scm` | LLVM IR |
| or eval | `eval.scm` | interpret the CPS |

The CPS form is the centre of the design.  It has seven constructs.  A
`letcont` is a basic block with parameters and an `appk` is a jump that
supplies them, so it is SSA with block arguments in place of phi nodes.
Every operand of every primitive is a named variable.

### The evaluator

`gaz -eval file.scm` runs `main` by interpreting the CPS over bignums,
reducing each result to its declared width.  `print` only works here.
This is what `tests/run.py` checks, and it is worth more than its size
suggests: it is an executable definition of what a Gaz program means,
independent of any backend.

## Sizes as type variables (proposed)

### The problem

`(vec 16 i32)` is fine for ChaCha20.  For bignum code it means one copy
of every routine per operand size.  The experiment on this branch adds a
size that names another argument:

    (define (i31/zero:none len:i32 x:(mut (vec len i32))) ...)

This is a small fragment of dependent typing: types indexed by a value,
where the index may only be the name of an immutable integer.  Nothing
is ever evaluated inside a type, so checking stays decidable and cheap.
Dependent ML and ATS work this way, and Futhark's size types are nearly
the same design.

### Where the experiment stands

Inside the callee it works: `(vec len i32)` unifies only with itself.
Two things are missing.

- **Call sites are not checked.**  `undyn-type` replaces each named size
  with a fresh variable, which discards the link between the length
  argument and the vector.  The original `test/i31_2.scm` calls
  `(CCOPY 1 len v1 v0)` against a signature of `(len ctl dst src)`, and
  it type-checks.
- **Types now contain term variables**, so every pass that renames or
  substitutes variables has to walk types as well.  `alpha.scm` and
  `rewrite.scm` both grew code for this, and the rewriter's was still
  being debugged when work stopped.

The LLVM backend also prints such a type as `[%len x i32]`, which is not
valid IR.

### The plan

Keep term variables out of types.  A size is an ordinary *size
variable*, and an integer may carry one as its index.  The definition
above is sugar for

    forall n.  (len : i32 whose value is n,  x : (mut (vec n i32)))

- In the callee, `n` is rigid: it unifies only with itself.  `unify`
  needs no environment.
- At a call, instantiate `n` fresh and let the vector arguments
  determine it by ordinary unification.  Then check that the index of
  the length argument equals `n`.  This is the step that is missing
  today.
- An integer literal `67` has index 67.  A formal parameter has its own
  rigid index.  Any other value gets a fresh index that equals only
  itself, which is sound: an unknown length matches nothing but itself.
- Do the check on the CPS, where every argument is already a name.
- The backend needs one map: size variable to the runtime value that
  holds it.

This also unifies the two kinds of size already in the type
representation.  A quoted variable `'n` is a size fixed at compile time
(specialize the function per use, as for P-256); a named one has a
runtime witness (as for RSA).  They are the same variable with or
without a value behind it.

### Later

- **Arithmetic.**  A product is `2n` limbs; BearSSL's i31 format is
  `n+1` words.  Normalize sizes to linear forms (`a*n + b*m + c`) and
  compare them syntactically.  No solver is needed.
- **Bounds.**  Indexing is unchecked today, which contradicts "no
  undefined behavior".  With size variables there is a cheap fix: the
  index variable of `(for (i:i32 len) ...)` is known to be below `len`,
  so indexing a `(vec len T)` with it is safe by construction.  Other
  indexes must be literals or be rejected.

## Secrecy labels (proposed)

This is the feature that would make Gaz a language for cryptography
rather than a small typed IR.

**A label, not a wrapper.**  Every type is `public` or `secret`:
`(secret i32)`, `(mut (vec 32 (secret i8)))`.  A public value may be
used where a secret one is expected, never the reverse.  Pointers,
sizes and loop counters are always public.

**The same operators.**  The result of a primitive is secret if any
operand is.  Labels are written only in function signatures; inside a
function they are inferred.

**A secret may not appear** as

- the condition of an `if`, or anything else that decides a jump,
- a vector index,
- an operand of `/` or `mod`, or of any primitive whose timing depends
  on its operands,
- a value stored to a public location or returned as a public result.

Because a secret can never steer control flow, there are no implicit
flows to track, and none of the program-counter machinery of general
information-flow type systems is needed.

**Two primitives** make this usable:

- `(select c a b)` takes a secret `i1` and compiles to a conditional
  move or a mask.  Comparisons on secrets are allowed; they produce a
  secret `i1`, which can only feed `select` or more arithmetic.
- `(declassify x)` is the explicit, greppable escape: releasing
  ciphertext, the final verdict of a MAC check, rejection sampling.

**Implementation.**  Not through the unifier, which solves equalities;
labels need "at most".  A separate pass over the typed CPS: each
variable's label is the join of what flows into it, block parameters
join over their `appk` sites, and loops iterate to a fixed point, which
with two labels is immediate.  Then check the restricted positions.

Three things in the current language would be rejected on secrets, and
are worth knowing about now:

- `and` and `or` expand to `if`, so they branch.
- `/` and `mod` become `udiv` and `urem`.
- `if` always compiles to a branch.

The guarantee holds in machine code only if nothing after this pass can
introduce a branch.  That is the argument for the next section.

## Backends

### Why not LLVM

LLVM was the right way to get started: typed, SSA, and many targets.
But its optimizer is free to turn a branch-free select into a branch,
and has done so to real cryptographic code.  It also brings undefined
behavior back in: division by zero, shifts by the width or more, and
out-of-range `getelementptr` are all undefined or poison.

### Direct output (proposed)

Emit assembly for arm64 and amd64 directly.  The CPS makes this much
smaller than it sounds:

- blocks with parameters and named operands: linear-scan register
  allocation, with moves at jumps;
- no closures, no heap, no garbage collector, no exceptions;
- calls only to known top-level functions, using the C calling
  convention at the boundary;
- each primitive maps to one fixed instruction sequence, chosen from
  the instructions the vendors document as data-independent (Arm DIT,
  Intel DOIT).

Irken has since grown hand-written arm64, amd64 and riscv64 backends,
and their assembler plumbing can be borrowed.

What LLVM was doing for free, and what replaces it:

| LLVM gave | Replacement |
| --- | --- |
| `i128`, `i256` arithmetic | `addc`, `subb` (add and subtract with carry) and `mulwide` (64x64 to 128) as primitives; wide integers become macros or library code over them |
| vector types and `shufv` | scalar code first; explicit SIMD types later |
| the vector-or-array distinction | gone |
| optimization | the existing rewriter, plus unrolling of fixed loops |

Carry and widening multiply are what bignum and field code is written
in anyway, and they map directly to `adc`/`adcs` and `mul`/`umulh`.

## Signedness (proposed)

No signed types.  Where signed behavior is needed it is an operation on
bit patterns, as in LLVM, WebAssembly and RISC-V: arithmetic shift
right (`ashr` already exists), signed high multiply, signed compare.
Overflow always wraps.  Lattice cryptography is the case that needs
these: its reference code keeps coefficients as signed 16-bit values
with Montgomery and Barrett reduction.

## What the algorithms need

| | Sizes | Arithmetic | Needs from Gaz |
| --- | --- | --- | --- |
| Hashes, ciphers | fixed | 32/64-bit, rotates | works today; runtime-sized input for absorbing messages |
| RSA | runtime | multi-limb, Montgomery | named sizes, carry and widening primitives |
| Elliptic curves | fixed per curve | 4 to 10 limbs, per-prime reduction | carry and widening primitives, `select`, constant-time table lookup; macros to generate reduction code |
| ML-KEM, ML-DSA | fixed (256 coefficients, rank 2 to 4) | 16- and 32-bit modular, number-theoretic transform | signed operations; branching on public data; SIMD for speed |

Two lessons from the post-quantum side bear on the design.  The
"KyberSlash" timing attacks came from a division on secret data, and a
separate bug came from a compiler turning a branch-free select back into
a branch.  Also, "no branching" is too strict as stated: rejection
sampling loops on public data, and ML-DSA signing retries by design.
The rule is "no branching on secrets".

A field-element type whose `+` and `*` map to named functions (the
`define-type-operators` idea in `notes/bmint.txt`) would let point
formulas be written as they appear in papers.

## Verification

In increasing order of cost:

1. **Differential testing.**  Run every generated routine against the
   evaluator on random and edge-case inputs.  Cheap, and catches most
   backend bugs.
2. **Translation validation.**  Do not prove the compiler; check each
   output.  For unrolled, loop-free code, an SMT solver can confirm that
   the emitted assembly computes the same function as the CPS.
3. **Export to a proof assistant.**  A Gaz function is nearly a pure
   function on fixed-width bit vectors already, and a fixed loop is a
   bounded fold.  Emitting Lean or Coq definitions from the typed core
   would allow proofs that, say, a field multiply equals multiplication
   mod p.

A verified compiler is out of scope.

## Known problems

- Calls to functions with named sizes are not checked (above).
- The LLVM backend emits invalid IR for named sizes, and prints `none`
  where it should print `void` in a `declare`.
- Vector indexing is unchecked.
- Primitive type signatures are Irken functions (`solve.scm`), not data.
  A small signature language would let the secrecy pass and the backends
  share one table.
- `unify` takes an environment argument that it does not use.
- `two**n` in `eval.scm` computes 2^(n+1).  Its one use is unaffected.
- The evaluator works around a `big-rshift` failure in Irken's
  `lib/bignum.scm` (`big-rshift*`).

## Order of work

1. One native backend (arm64 or amd64), checked against the evaluator
   on the existing tests.  Retire `llvm.scm`.
2. `addc`, `subb`, `mulwide`, `select`.
3. Secrecy labels.
4. One piece of field arithmetic as the proof: X25519.
5. Size variables, replacing `itype:dyn`.
6. Signed operations, then ML-KEM.

## Related work

- **qhasm** (Bernstein): portable assembly with named variables.
- **Jasmin**: qhasm's successor, with a verified compiler and a
  constant-time type system.  The closest thing to Gaz's goals.
- **FaCT**: a C-like language with secret and public labels.
- **fiat-crypto**: field arithmetic generated from the prime, with proofs.
- **Cryptol**: a specification language with size-polymorphic types.
- **Futhark**: size types very close to the plan above.
- **Dependent ML, ATS**: the index-variable approach to dependent types.
- **BearSSL** (Pornin): the constant-time idioms and the i31 bignum
  layout that `tests/i31.scm` follows.
