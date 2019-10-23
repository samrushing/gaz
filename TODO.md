
TODO
----
* add [types]
* handle and propagate [annotations].
* use sexp-match to do the parsing.
  [I think the answer is *no*, see sexpat below]
* consider making clexp:let n-ary rather than devolving it into let*.
* convert var/cvar to int
  (this turned out to be a Bad Idea - rewrite all hosed because no distinction)
  might want to explore this again later using a real datatype for the various
  var types.
* add functions (maybe?)
  Thought I needed functions for loops, but if instead I expose 'appk' to the user
    we can implement loops/recursion directly with conts.  I think.

sample application
------------------

A good 'first light' test of the compiler would be the 'nearly divisionless'
random interval algorithm:

    uint64_t
    nearlydivisionless ( uint64_t s, uint64_t (* random64 ) ( void ) ) {
      uint64_t x = random64 () ;
      __uint128_t m = ( __uint128_t ) x * ( __uint128_t ) s;
      uint64_t l = ( uint64_t ) m;
      if (l < s) {
        uint64_t t = -s % s;
        while (l < t) {
          x = random64 () ;
          m = ( __uint128_t ) x * ( __uint128_t ) s;
          l = ( uint64_t ) m;
        }
      }
      return m >> 64;
    }

And of course one of the good PRNG's.

sexpat
------

*can* we use this as a parser?
the problem is that we want it to transform
code at compile-time.
e.g.:

    (sexp:symbol 'i32)  -> i32
     (sexp:list ((sexp:symbol 'vec) (sexp:int size) type))
     -> (type/vec size (parse-type type))

What would this look like as a sexpat?

    <i32> -> i32
    (<vec> n t) -> (type/vec n (parse-type t))

So the problem with this is that it doesn't enforce that `n` must
be an integer.  So any pattern language that would do that would
have to look something like this:

    (<vec> (!int n) t)

Which of course isn't much of an improvement over 'normal' sexp
pattern matching.  About the only place where we could get help
would be to automate somehow the handling of annotations.  But
I think that can probably be done with some kind of 'best practice'
that I haven't completely figured out yet.

types
-----
we need to extend the universe of values.
previously we had `cons` & `int`.  for crypto we want
  the T=i<n>|<vector T> typeset.  we also probably need
  a separate `ref` type.  But what can it contain?
  [or yet, like in smlnj is a ref type equiv to a length-one vector?]
ok, I've added typed variable bindings (in define, let, and let-loop).
the next step is to infer/propagate all types.
  * parse literals
  * compile top-level literals as data.

I've realized that we can't really just wing this, there are certain
problems that really want tvars-and-unification.  For example:

    (+ 1 2 3)

Here we are making no references to bound variables, so we have three
integer arguments of unknown type.  So the type scheme for `+` cannot
figure out what type to attach to the prim call.

The same issue will probably come up with calls/args to other functions,
so doing it 'right' just makes sense.

### literals

Our literals will be fairly simple: either integers (of TBD size), or
vectors.  I think we can make multi-dimensional vectors by simply
writing the literal out and then checking its dimensions, and giving
it a type like `(vec 5 't0)` or `(vec 3 (vec 3 't0))`.


annotations
-----------

leaning toward just handling annotations 'manually', rather than
coming up with some fancy automated system like sexpats.

Assume we can parse an expression with annotations.  So parse-clexp
will give us two results: an annotation and a `clexp`.  How do we
attach that information to the `clexp`.  And then, how do we propagate
that into the `cps` (and potentially all the way down to llvm)?

One idea I've been tossing around (similar to how I'm approaching type
info) is to attach an integer to every node in the tree, and then keeping
a map from that integer to the annotation info.  We could even 'parse'
the annotation and put it into a proper data structure.

### another idea

The current annotation sexp is super annoying. It'd be nice to have
a `sexp:ann` which would be much easier to match against.  But we don't
want to go back and change all of irken to do this.

As a compromise, we could introduce `asexp`, with `asexp:ann` being
the only change, and add a translation step. [this is totally in the
micro-pass oeuvre].

### that doesn't really help all that much.

I think the only 'clean' way to do this is to make a specialized pattern
matcher that somehow catches and passes annotation info down (if it's
wanted).  This takes us back to the comment in the 'sexpat' section where
there's "no advantage" to a separate syntax.  Well, except for dealing with
this fucking annotation problem.

What might the syntax look like?

    (sexp:list ((sexp:symbol 'define) (sexp:list ((sexp:symbol name) . formals)) . body))

We want this translated automatically into:

    (A 0 (sexp:list ((A 1 (sexp:symbol 'define)) (sexp:list ((A 2 (sexp:symbol name)) . formals)) . body)))

where `(A 0 ...)` indicates annotation 0.  Are these annotations useful in this form,
or do we just want to provide the 'outer' one only?

The input syntax might look like:

    ((:sym 'define) ((:sym name) . formals) . body)

Other tags might be:

    (:int) (:bool) (:string) ...

Handling records might be tricky, but probably necessary, since we want to be able
to use this to parse full languages.

### sexp-parsing language

Now we explore the above idea.  What's the UI look like?

    (sexp-match exp
      ((:sym 'foo) (:sym name) (hd . tl) . body)  -> <match-0>
      ((:sym 'bar) (:int n) . body)               -> <match-1>
      ...
      )

Every 'item' in the pattern has its annotation captured, _except_
for the tails of lists. [theoretically we could capture the first
item's annotation and feed that?]

Each annotation will be numbered, left to right, as follows:

    0 1           2           3 4    5?     6?
    ( (:sym 'foo) (:sym name) ( hd . tl ) . body)

So the annotation should be quite predictable.

Question: how to handle matching `(list sexp)`?  For example, in `(hd . tl)`
above, there's no way to avoid having `tl` being a list rather than a sexp.
I think we'll need the usual companion fun, `sexp-match-list`.

### ok, that actually _worked_

However.  The generated code is ENORMOUS.  Just matching
`((:sym 'foo) (:sym bar) (:int 3))` generated a 605-line function.

So I think I need to revisit this.  Same language, but make a data
structure that is walked at runtime.  The trick will be getting the
variables bound for the user code.


### runtime sexp matching

This seems to work.  Trying to figure out how to extract values as the
correct types for the user code.  The easiest would be to bind everything
with a let pattern.

    (sexp-match exp with
      (<let> (:list binds) . body) -> user-code
      ...)

Here, `body` and `binds` will both be bound to `(list sexp)` vars.

    (let ((mvars (domatch <compiled-sexpat-literal> exp)))
      (match mvars with
        (maybe:yes vars)
        -> (let ((binds (tree/get vars symbol-index-cmp 'binds))
                 (body (tree/get vars symbol-index-cmp 'body)))
             user-code ...)
        (maybe:no) -> failure-code ;; no match
        ))

We need to pull non-sexp types out.
Now, how do we provide the annotations?  How about this:

    (let (((binds binds-ann) (tree/get vars symbol-index-cmp 'binds))
           (thing0 thing-ann) (tree/get vars symbol-index-cmp 'thing))
           thing (sexp/int thing0)
          ...)
      user-code ...)

If we want to integrate this into the irken compiler, we'll need the
compile-time and runtime components.  At runtime, we'll need the matcher
function and functions like sexp/int, sexp/bool, etc...

Now, how do we translate this thing?

TWO MONTHS LATER
----------------

### parser combinators

A simple idea, maybe... but the devil is always in the details.

Now we have a parser combinator library, and a parser built with it
that can correctly parse s-expression grammars.  It propagates src
info directly into the resulting AST.

Remaining tasks:

  * either:
    * add a 'fail' arm to the 'result' type.
    * add a boolean to `result:no` that indicates if this is a full
      failure and to abandon any further attempts to parse.
  * build a 'custom' PC that will trigger a fail when a particular
    form fails to parse.  i.e., don't let a malformed 'let' be later
    treated like a bad funcall.
  * swank error reporting: take advantage of the metadata attached
    to the parser to show exactly what it was doing when it failed.
    e.g. "failed to parser initializer in this let binding here".
  * ... eventually plug the parser back into the compiler and continue.

Ok, much of the above is working.  I'm still not happy with the
result, though: there are too many 'map' functions, so still lots of
hand-written code that should instead be data-driven.

Thoughts:
  * start with the ideas of parser combinators, but write something
    that's less monady and more irkeny. [i.e. something more amenable
    to a DSL to generate all the code - one that supports 'actions']
  * change the 'inner' function design to take two arguments: src and
    input, rather than just input?
  * instead of the 'zparse' data structure, maybe we could have something
    that's either 'sexp' or '(list sexp)', where the list is used for
    opt, plus, and star.
  * to experiment, start with the type parser, since it shakes out most
    of the issues.

