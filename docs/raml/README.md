## Some notes on Resource Aware ML
[kwxm: I'll add the files later]

### Introduction
In [[HJ2003](#hj2003)], Martin Hofmann and Steffen
Jost describe a static analysis which infers heap space bounds for
first-order functional programs.  The analysis involves a type system
which describes constraints on heap space usage in a compositional
way.  The analysis works for programs involving algebraic datatypes
and can produce bounds which are _linear_ in the size of objects: for
example it might infer that a function taking two lists `l1` and `l2`
requires `4x + 2y + 10` heap cells, where `x` is the length of `l1` and `y` is
the length of `l2`.  Constraints arising from individual typing rules
are aggregated and passed to a [linear
programming](https://en.wikipedia.org/wiki/Linear_programming) solver,
which automatically produces overall heap space bounds for
individual functions and an entire program.

The analysis was later extended to handle single-variable polynomial
bounds in [[HH2011](#hh2011)] and multi-variable polynomial bounds
in [[HAH2012](#hah2012)].  These extensions reduce polynomial bounds
to collections of linear bounds, using a clever re-indexing techinque to
deal with recursive invocation.  This is important because analysis of
non-linear functions is a very difficult task in general, whereas
linear bounds can be dealt with using linear programming, which is
well-understood and has efficient implementations.

These analyses are not limited to heap space usage, but allow analysis
of more general computational _resources_, such as execution time or
file handle usage.

Note that the problems of deciding time and heap usage are both
undecidable in general, since both subsume the halting problem.  In
the case of time, we're asking not just whether a progam halts, but
how long it takes to do so.  To see that space usage is undecidable,
take any program and insert operations which allocate heap space along
every possible execution path: the heap usage will then be finite if
and only if the program terminates, so even deciding whether heap
alloction is finite is as hard as deciding termination.

### RAML

The techniques mentioned in the introduction have been further
extended and implemented in the [Resource Aware ML](#raml-website)
(RAML) project led by Jan Hoffmann.  The RAML language is a subset of
OCaml containing standard functional features such as algebraic
datatypes, polymorphism, and higher order functions, but omitting some
of the more complicated features of OCaml such as records, objects,
and modules.  RAML also includes some extensions such as a destructive
match which releases the heap space used by an object and makes it
available for re-use.

#### Implementation
The current RAML implementation (as of January 2019) has the following
features, amongst others.

* An evaluator which will run RAML programs and print the number of
  evaluation steps and the heap space used.  RAML also includes a
  `tick` function which can be used to tell the evaluator that some
  quantity of a user-defined resource (for example, bytes transmitted
  along some channel) and the evaluator will also print the total amount of
  resources consumed by `tick`.

* An analyser which performs static type analysis of RAML programs and
  reports resource usage.  The analyser can infer upper (worst-case)
  and lower (best-case) bounds on heap-space usage, evaluation steps,
  and resources consumed by `tick` (see above).

The implementation is quite complex: the analyser contains almost
25,000 lines of (quite dense) OCaml code and the evaluator almost
12,000 lines. This does not include code for parsing: for this, RAML
reuses the standard OCaml parser (about 6000 lines in total, including
input to the OCaml lexer and parser generators).  In addition, the
analyser makes use of the [Clp](https://projects.coin-or.org/Clp)
linear programming solver, comprising over 318,000 lines of C++ source
code and 100,000 lines of headers.

#### Performance

RAML comes with a large number of example programs, some written by
the RAML implementers and some taken from other people's codebases
(note that since the RAML language is essentially a subset of OCaml,
RAML can be used to analyse real OCaml code).

The examples are generally natural OCaml code that hasn't had to be
specially tailored so that RAML can deal with it.  For most of the
examples the RAML tool can analyse the code in a few seconds and
produce upper bounds on both heap usage and number of execution steps.
When programs are run using the RAML evaluator, the actual space and
time usage generally agree precisely with the predictions (at least in
cases where the worst case actually occurs).


#### Limitations

RAML has a number of limitations.

* It can only deal with code where the bounds are polynomial: it can't
  handle bounds such as `2<sup>n</sup>` or `n.log n`. In the former
  case the analysis will fail (reporting an infeasible linear program;
  in the latter case, RAML might report a bound of `n<sup>2</sup>`,
  which would be a correct bound but not a precise one (I haven't
  actually tried this: whether RAML could find an overestimate like
  this would depend on exactly how the program was implemented).
  * It's conceivable that RAML could be extended to include special
    cases such as logarithmic and exponential bounds by recognising
    particular patterns of computation, but it seems most unlikely
    that it could be extended to deal with completely arbitrary
    bounding functions.

* Like most static analyses, the RAML analysis is incomplete: there
  will be cases where a program can be proved to have a certain heap
  usage, but RAML can't discover it.  This is inevitable, since resource
  usage analysis subsumes the halting problem.

* Complex use of higher order functions can be problematic.  For example,
  a partially-applied function `f` might capture a list `L` and the resource
  usage when `f` was eventually fully applied could depend on the size of `L`;
  the RAML type system can't deal with situtations like this.

* RAML only works on functions which iterate over algebraic datatypes,
  and can't deal with things whose resource usage depends on numerical
  inputs.  For example, if we had a function to create the list `L =
  [1..n]` then RAML would be able to recognize that the resource usage
  would depend on the length of `L`, but would not realize that this
  is equal to `n`.  There are analyses which can handle numerical
  inputs (see [Other Analyses](#other-analyses) below), and in principle these could be combined with
  the RAML techniques.  This would be a lot of work though, and it's
  more of an implementation problem than a research problem, so it's
  probably not something that's worth the RAML implementers' trouble.


* Actual resource usage of course depends on the behaviour of compiled
  code.  The RAML evaluator is quite straightforward and doesn't make
  any attempt to perform optimisations, so predictions conform well to
  runtime performance. However, an actual compiler will usually
  perform complicated code transformations which might affect resource
  usage.  Ideally these would be optimisations, but it's conceivable
  that a supposed optimisation might backfire in some cases, leading
  to an increase in heap usage or increased execution time.  This
  disconnect is inevitable unless one has a formal cost model of the
  source language and a proof that the compiler/evaluator preserves
  costs (or at least transforms costs in a predictable way).

  * A related issue is that a compiler may allocate objects on the heap
    (closures, for example) which aren't obtained from datatypes in the
    source program.  HOW DOES RAML DEAL WITH THIS?

### RAML and Church/Scott encoding

We're interested in whether RAML can be used with the Scott encoding
used in Plutus Core.  RAML depends heavily on algebraic datatypes, so
it's not immediately clear that it's applicable to types encoded as
higher-order functions.  However, the technique of
_defunctionalisation_, due to John Reynolds, can be used to convert
higher-order programs to first-order ones, representing higher-order
functions as members of algebraic datatypes (essentially closures
represented in the source language).  I tried some examples with Peano
numbers to see if this would make Church and Scott encoded data amenable
to RAML analyses.

#### Standard Peano numbers

The file [Peano.raml](./Peano.raml) contains a simple RAML program involving Peano numbers.
The output of RAML's analyser is in yyy, and the output of the
evaluator, including the actual resource consumption, is in zzz.  As
can be seen, RAML is able to predict the resource usage precisely. The
RAML documentation doesn't describe how members of algebraic datatypes
are represented in the heap, but examination of the intermediate code
suggests that a Peano number requires 4 heap cells for each `S`
constructor and 2 for the `Z` constructor.


RAML gives the heap bounds `4*M` for addition of the Peano numbers,
and `4*M*N+2` for multiplication, which are correct (addition reuses
the second argument and only has to allocate cells for a copy of the
first argument, but mulitplication allocates heap cells for the whole
of the product, including a Z node).  Since RAML can only deal with
polynomial bounds, it isn't able to come up with a bound for
exponentiation, reporting an infeasible linear program.

RAML can also predict bounds for the number of evaluation steps: see
xxx.  It's more difficult to see whether these are correct because
evaluation is more complicated than heap allocation, but the results
reported in xxx do agree exactly.

#### Church-encoded Peano numbers

A Church-encoded version of the test program appears in xxx, and a
manually defunctionalised version in yyy.  Defunctionalising the
Church encoding yields something very similar to the original program
in xxx1 (this is no surprise: see [Danvy]), so RAML is again able to
produce good results (see uuu).  Somewhat surprisingly, RAML also
produces good predictions for the version using higher-order
functions: see xxx and yyy.  I don't know what to make of this.

#### Scott-endcoded Peano numbers

I wasn't able to use the Scott encoding directly in RAML or OCaml, due
to restrictions of the OCaml type system.  It is possbile to use the
Scott encoding using records in OCaml (see ttt), but RAML can't deal
with this because it doesn't support records.  Other methods for
embedding complicated System F types and terms are described in
[[Lindley2012](#lindley-2012)], but again these use features of OCaml
which aren't supported by RAML.  Thus I wasn't able to get any results
for the Scott-encoded Peano numbers.

[I was trying to defunctionalise the Scott encoding to see what happened,
but had some difficulty and then had to do something else. I'll look at
this again later.]

--------
### Other Analyses

There is a considerable amount of literature on static resource analysis.
The following subsections contain brief descriptions of some other techniques.
[... or they will do at some point]

#### SPEED
https://www.microsoft.com/en-us/research/publication/speed-precise-and-efficient-static-estimation-of-program-computational-complexity-2/

#### COSTA
http://costa.fdi.ucm.es/costa/costa.php

#### Lattice point enumeration in polytopes

#### Implicit Computational Complexity

--------
## Conclusion

The RAML analysis is strongly based on algebraic datatypes, and this
makes it inapplicable to Plutus Core.  It might be possible to adapt it
to work with PlutusIR or some defunctionalised version of Plutus Core,
but full PlutusTx would probably be too complex a language to deal
with.

RAML alone is not suitable for programs where recursion or iteration
is controlled by numeric values: to deal with these we'd also need
some analysis such as one of those mentioned in the previous section.
Things are complicated by the fact that Plutus Core doesn't have
explicit contructs for recursion or branching, which makes it very
difficult to construct a control flow graph, something which is
central to many static analysis techniques.  Again, an intermediate
language with suitable constructs might help with this, although we'd
need some guarantees about the translation to Plutus Core in order to
be sure that any bounds derived from the intermediate language were
applicable to code which is actually executed.

It's conceivable that techniques from implicit computational complexity
would be directly applicable to Plutus Core, but I don't know how
usable these methods are in practice.

--------

#### References

##### RAML website
http://raml.co/

##### HJ2003
M. Hofmann and S. Jost.\
Static prediction of heap space usage for first-order functional programs.\
POPL '03.\
[pdf](http://www2.tcs.ifi.lmu.de/~jost/research/POPL_2003_Jost_Hofmann.pdf)

##### HH2011
Jan Hoffmann and Martin Hofmann.\
Amortized Resource Analysis with Polynomial Potential -
A Static Inference of Polynomial Bounds for Functional Programs.\
ESOP '10.\
[pdf](http://www.cs.cmu.edu/~janh/papers/aapoly_extended.pdf)

##### HAH2012
Jan Hoffmann, Klaus Aehlig, and Martin Hofmann.\
Multivariate Amortized Resource Analysis.\
TOPLAS, 2012.\
[pdf](http://www.cs.cmu.edu/~janh/papers/aa_popl11.pdf)

##### Lindley2012
S. Lindley.\
Embedding F.\
WGP '12.\
[pdf](http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf)
