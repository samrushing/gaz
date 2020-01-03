
TODO
----

* try to detect array-vs-vector via usage and automatically Do The
  Right Thing.  if possible.
* itype:name - an integer type that points to a variable, used to
  state that a vector length is available in a variable.  Can this
  work, and can it be safe?
* implement real type schemes for prims [maybe put them in basis?]
* tag prims with 'side-effect' nature. [so dead-prim can work]
* explore type for bigmodints (i.e., i31)
  [I think this will require a typing phase at the zexp level,
   in order to swap out 'prim +' with 'call particular funciton']
* debugger for evaluator
* problem with let-loop binding environment.
* remove unnecessary apply-subst
* [optional?] clear alloca
* mem2reg (i.e. something like an SSA conversion for assignments)
* sanity check type/size/etc vector literals.
* $gensym in mbe.
* verbose flag.
* annotations: combine src into srcs.  separate pass?
  might want the src datatype to handle this for zexp.
* real error reporting with lots of nice colors.
* start looking into vector operations.
  [might need some sample algorithms to facilitate]
* start exploring dependent types.


DONE
----

* typing pass for zexp.
* bigint in read.
* letcont form.
* define-constant/define-mutable.
* kinding of types.
* compiler options
* evaluator
