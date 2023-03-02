# An Overview of Built-in Types and Functions

The Plutus ledger languages are parameterised by the built-in types and 
built-in functions they supports.

## Built-In Versions

A built-in version is a fixed set of built-in types and built-in
functions. Each Plutus ledger language supports a particular built-in
version.

Therefore, a built-in with the same name may or may not exist in
different versions and its type and implementation might change across
versions.

Hence, it is useful to think of a built-in as being indexed by its
version. We may write this as a built-in name with its version as a
subscript. For example, the built-in function `ifThenElse` at
version 1.1 may be written as `IfThenElse_1.1`. For a formalisation,
having the version as an index, rather than a parameter, fits better
with the fact that a built-in might only exist at a certain version.

As a convention, the version may be left implicit. When the version is left 
implicit, the version should be clear from the context. Without the version 
we cannot talk about a built-in's existence, type, or denotation.

* In the implementation the version is a
  parameter of the built-in in the call to function
 `toBuiltinMeaning`.
* In the specification, a set of atomic types, a
  set of type operators, and a set of built-in functions is assumed.
  Built-in functions are given by a name, a signature, and a
  denotation.
* The current formalisation only supports one
  fixed set of builtins.

## Requirements
   
### Implementation requirements
   
The implementation of Plutus Core has a generic mechanism for adding
built-ins which is extremely flexible.
The implementation of the built-in can be roughly any Haskell
function whose type can be inferred and mapped to a Plutus Core
type.

Let us call this function the *underlying implementation* of the
built-in function. The generic mechanism will lift the underlying
implementation to an actual Plutus Core function, which we call the
*induced built-in function*. Since we have as a requirement that the
type of the underlying function can be mapped to a Plutus Core type,
the induced built-in function can also be lifted to a Typed Plutus
Core function.
   
Type constraints are not allowed. An underlying implementation may
choose to instantiate constrained types (for example, using type
application or type annotations) in order to fix the typeclass
instance to one specific type and hence avoid type constraints in
the denotation.
  
The function must be pure, except for, possibly, the following effects:
1. Logging (the implementation returns a result
using the `Emitter` monad).
2. Failure (the implementation returns a result
wrapped in EvaluationResult)

In particular, throwing exceptions is not allowed.

Logging only appears in the implementation and does not affect the
on-chain behaviour. Hence, it is not relevant for the specification
or the formalisation.

Builtin functions must take at least one argument (either a type or
    term). That is, nullary functions are not allowed. 
    
A limitation of the implementation is that type variables in 
polymorphic return types must have a type tag. Therefore the tag type
should be inferrable from somewhere. Notably, the following 
built-in function constructing a polymorphic empty list is not allowed
because there would be no way to know the type of the empty list.

```
nil : forall a. list a
```

The workaround currently used in the implementation is to provide monomorphic
built-in functions for the empty list (see `mkNilData` and `mkNilPairData`).


#### On built-in support of the implementation

Due to its flexibility, the current implementation supports a wide
variety of built-in functions with strange semantics[^1]. These strange
semantics are obtained by exploiting details of the implementation
in order to, for example, check the type tag of the
argument.

Functions with strange semantics should be avoided despite being
implementable. Adding such functions would complicate the correct
specification and formalisation of the builtin, as well as making
the semantics dependent on the current details of implementation,
seriously limiting the scope of future changes. So, even when the
implementation has the power to run built-ins with strange
semantics, it would be advisable to ban their addition.

The question is how to characterise what is and what isn't a good
semantics. We have two types of additions:

1.  Built-in types, and their constants and
    introduction and elimination operators,
2.  Built-in functions (not covered in the
    previous point).

We propose that the induced built-in functions should be
expressible in Typed Plutus Core[^2] (modulo the effect of logging which
has a special status). That is, built-in functions should not extend
the possible semantics. Extending the model by adding a built-in
function not representable in Plutus could be a potential *security
concern*, as the interaction of a non-standard semantics with the
rest of the language is not guaranteed to be safe, or to respect the
cost model. A new built-in function that extends the possible
semantics would require rethinking the whole specification,
formalisation, and cost semantics, so the bar for the addition of
such a built-in should be set extremely high.

[^1]: For some examples see `plutus-core/examples/PlutusCore/Examples/Builtins.hs`.
[^2]: Asking for a typed implementation, rather than untyped Plutus Core, gives 
  further guarantees of good behaviour.

#### Correspondence of Plutus types and Haskell types

Plutus' `integer` corresponds to Haskell's `Integer`. If
the denotation has in its type `Int`[^3], `Int64`, or
`Word8`, these types will be automatically converted to/from
`Integer` after an underflow/overflow check.

[^3]: The type `Int` is convertible only if it’s equal to `Int64` 
  (32 bit systems are not supported).

### Specification Requirements
Builtin functions must take at least one argument (either a type or term).

In the specification there is a distinction between variables that
range over built-in types $v$# (type operators such as `list`
may be applied to these variables), and variables that range over
any type $v⋆$ (such as the case of `ifThenElse`). However this
distinction is not currently made in the implementation.

Let's call *composite built-in types* types obtained from either
built-in types or saturated built-in type operators applied to
composite built-in types. All the arguments must be either a
composite built-in type or a (general) type variable. One
consequence of this requirement is that no higher-order arguments
are allowed.

Polymorphism over built-in type operators is not allowed. For
example, a built-in function of the following type is not allowed:
```
forall f. f integer -> bool
```

The specification allows for universal quantifiers to be
interleaved with any types, but the scope is always the rest of the
type, including the return type. If we compare with the case where
quantification of type variables is the outermost operation, the
generality of adding quantifiers in the middle does not seem to gain
any expressivity. Furthermore, it\'s not used in any of the current
built-ins, for which all polymorphic built-ins have their
quantifiers at the beginning of the type. Note: Because type
application gets translated to a `force` operation on `uplc`,
there could be a difference in expressivity regarding errors.
However currently, no built-in function uses this corner case.

Built-in functions are given semantics by a mathematical function,
and hence all functions are terminating. While, in principle, one
could allow non-terminating functions, requiring termination makes
things much simpler for specifying and formalising semantics and for
modelling costs.

### Agda Formalisation Requirements

Implements 35 built-in functions of the 54 built-ins supported by
the implementation.

The executable plc-agda ultimately maps the meaning of built-in
functions to a Haskell function (often, the same function that is
the first argument of `makeBuiltinMeaning` in the
implementation). In order to get the results of the execution of a
built-in function back into Agda, results of the Haskell function
which are wrapped in `Emitter` are run with
`runEmitter` and results which are
wrapped in `EvaluationResult` are converted to a Haskell
`Maybe` (which can be interpreted as an Agda `Maybe` by
the Agda compiler).

There are 13 exceptions where the built-in function is implemented
using Agda code, rather than calling Haskell
functions:

* If-then-else (Agda semantics)
* addition (`Data.Integer.+`),
* substraction (`Data.Integer.-`),
* multiplication (`Data.Integer.*`),
* integer less than operator (`Data.Integer._<?_`),
* integer less or equal operator (`Data.Integer.\_≤?\_`),
* Integer equality (`Data.Integer.\_≟\_`),
* String append (`Agda.Builtin.String.primStringappend`)
* String equality (`Agda.Builtin.String.primStringEquality`)
* `iData`, `unIData`,`bData`, `unBData` (Agda Semantics).

The meaning of built-in functions is given three times in the
formalisation, the main part being functions named `BUILTIN` in:

1.  `Algorithmic/ReductionEC.lagda.md`,
2.  `Algorithmic/CEK.lagda.md`, and
3.  `Untyped/CEK.lagda.md`.

Only one version of built-in functions is supported. For example,
for `verifyEd25519Signature`, version 1
(`verifyEd25519Signature_V1`) is used.

The type of built-in functions is described by a signature.
A signature consists of the number of distinct type variables, a non-empty
list of parameters and a result, both of *built-in-compatible* types.
The built-in-compatible types coincide with the specification, except that 
they don't distinguish between variables of built-in types $v$# and general 
type variables $v⋆$. In that sense, it behaves like the implementation.

The signature is defined for all 54 built-in functions.

## Desirable properties

Built-in types are part of the core language, which means the whole
ecosystem relies on them. Therefore the ability to document them in 
a way that the community can easily understand is essential.

Built-in types should have a clear cost semantics.

Built-in functions should have the following properties:
* Terminating (this is expected by the specification).
* They must not throw any exceptions.
* Clear dynamic semantics. This is important as
  it should be possible to specify, formalise and communicate the
  behaviour of each built-in function in an effective way.
* Clear static semantics. Even though the built-in is ultimately run 
  in UPLC, an untyped language, it should make sense in Plutus and 
  typed Plutus Core, so it should have a proper type.
* Clear cost semantics.
* Testable. It should be possible to test the
  correctness of the function. There are many ways to do this: through
  provided tests, through specification of properties that must hold,
  through a (correct) reference implementation, or through a proof of
  correctness of the implementation.

#### Observations:

* The [CIP 35](https://cips.cardano.org/cips/cip35/) doesn't mention any requirement on
    the type of the new built-ins. However there are limitations. These
    limitations are given by the requirements of the PLC specification
    and of the implementation. No specification of the behaviour of the
    new built-in is required, nor proof of termination (only an
    argument). It is implicit that tests should be provided, as would be
    expected for any merge request.
* Since we are asking for pure terminating functions, one could ask for 
  an Agda implementation. One could then use this specification in `plc-agda`.
    Alternatively, one could ask for a reference Plutus implementation,
    which could be executed by plc-agda as the implementation of the
    given built-in. This would allow testing the reference Plutus
    implementation against the provided production implementation. In
    both cases, one could test that the semantics of the built-in
    function is "standard" (no semantics weirdness), that no exceptions
    are thrown, and ensure that it is typeable. The main limitation for
    this approach is that these implementations should be fast enough to
    be usable in testing.
* Although obvious, CIP 35 doesn't mention that the name of the new 
  built-in function shouldn't be in use as there is no support for 
  overloading built-in function names.

The formalisation defines the meaning of built-in functions thrice. 
Also there are three notions of value, and three notions of partial 
built-in function application. Code  duplication is a well-known anti-pattern
that leads to possibly inconsistent semantics, increased maintenance costs, 
decreased code readability, and increased type-checking and compilation times. 
So, it would be desirable to unify these definitions into a single, parameterised
one.

## Reference: List of Built-ins and Their Types

There are currently 54 supported built-in functions in the
implementation.
Obtained from the `uplc` command:

```
addInteger               : [ integer, integer ] -> integer
subtractInteger          : [ integer, integer ] -> integer
multiplyInteger          : [ integer, integer ] -> integer
divideInteger            : [ integer, integer ] -> integer
quotientInteger          : [ integer, integer ] -> integer
remainderInteger         : [ integer, integer ] -> integer
modInteger               : [ integer, integer ] -> integer
equalsInteger            : [ integer, integer ] -> bool
lessThanInteger          : [ integer, integer ] -> bool
lessThanEqualsInteger    : [ integer, integer ] -> bool
appendByteString         : [ bytestring, bytestring ] -> bytestring
consByteString           : [ integer, bytestring ] -> bytestring
sliceByteString          : [ integer, integer, bytestring ] -> bytestring
lengthOfByteString       : [ bytestring ] -> integer
indexByteString          : [ bytestring, integer ] -> integer
equalsByteString         : [ bytestring, bytestring ] -> bool
lessThanByteString       : [ bytestring, bytestring ] -> bool
lessThanEqualsByteString : [ bytestring, bytestring ] -> bool
sha2_256                 : [ bytestring ] -> bytestring
sha3_256                 : [ bytestring ] -> bytestring
blake2b_256              : [ bytestring ] -> bytestring
verifyEd25519Signature   : [ bytestring, bytestring, bytestring ] -> bool
verifyEcdsaSecp256k1Signature: [ bytestring, bytestring, bytestring ] -> bool
verifySchnorrSecp256k1Signature: [ bytestring, bytestring, bytestring ] -> bool
appendString             : [ string, string ] -> string
equalsString             : [ string, string ] -> bool
encodeUtf8               : [ string ] -> bytestring
decodeUtf8               : [ bytestring ] -> string
ifThenElse               : [ forall a, bool, a, a ] -> a
chooseUnit               : [ forall a, unit, a ] -> a
trace                    : [ forall a, string, a ] -> a
fstPair                  : [ forall a, forall b, pair(a, b) ] -> a
sndPair                  : [ forall a, forall b, pair(a, b) ] -> b
chooseList               : [ forall a, forall b, list(a), b, b ] -> b
mkCons                   : [ forall a, a, list(a) ] -> list(a)
headList                 : [ forall a, list(a) ] -> a
tailList                 : [ forall a, list(a) ] -> list(a)
nullList                 : [ forall a, list(a) ] -> bool
chooseData               : [ forall a, data, a, a, a, a, a ] -> a
constrData               : [ integer, list(data) ] -> data
mapData                  : [ list(pair(data, data)) ] -> data
listData                 : [ list(data) ] -> data
iData                    : [ integer ] -> data
bData                    : [ bytestring ] -> data
unConstrData             : [ data ] -> pair(integer, list(data))
unMapData                : [ data ] -> list(pair(data, data))
unListData               : [ data ] -> list(data)
unIData                  : [ data ] -> integer
unBData                  : [ data ] -> bytestring
equalsData               : [ data, data ] -> bool
serialiseData            : [ data ] -> bytestring
mkPairData               : [ data, data ] -> pair(data, data)
mkNilData                : [ unit ] -> list(data)
mkNilPairData            : [ unit ] -> list(pair(data, data))
```

The implementation does not distinguish between polymorphism over
arbitrary types and built-in types and therefore the output of the
`uplc` command does not make this distinction.
