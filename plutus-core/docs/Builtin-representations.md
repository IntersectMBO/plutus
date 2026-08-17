# Checked builtin representations

Some polymorphic builtins need runtime information that determines the layout of their result.
That information must be an explicit term: deriving it from a type during erasure makes erasure
builtin-aware and is not ordinary representation passing.

`MatchDataConstr` uses the following type scheme:

```text
MatchDataConstr : forall S. BuiltinRep MatchDataConstr S -> Data -> S
```

`BuiltinRep MatchDataConstr S` is an abstract builtin type family. Its values are checked runtime
directives indexed by the type produced when the directive is interpreted. It follows the
representation-passing discipline of lambda-R: the type index is erased, while the runtime
representation is an ordinary explicitly passed term. Unlike lambda-R's singleton-like `R(S)`,
this family can have many operationally distinct inhabitants at one index, because different
matching patterns can capture the same result shape. Guarded recursive datatypes/GADTs and typed
format descriptions are therefore closer structural analogies.

## Static rules

Write `BR_M(S)` for `BuiltinRep MatchDataConstr S`, `Decode(b) = P` for decoding a representation
constant, and `Capt(P)` for the SOP type of the fields captured by `P`.

Formation uses PLC's nominal, builtin-specific representation type former:

```text
Gamma |- S : Type
-------------------------
Gamma |- BR_M(S) : Type
```

The only typed introduction form is a builtin-specific checked witness:

```text
b is a constant    Decode(b) = P    ValidPattern(P)
----------------------------------------------------
Gamma |- builtinrep MatchDataConstr b : BR_M(Capt(P))
```

The checker obtains this rule from the representation metadata associated with `MatchDataConstr`. The
metadata validates the constant and synthesizes its complete indexed type. Ordinary application
then requires that type to equal the instantiated argument type `BR_M(S)`. Other builtins cannot
claim the witness, and PLC has no eliminator for the abstract family.

The implementation represents `BR_M(S)` directly as `TyBuiltinRep "matchDataConstr" S`. It is not a
member of `DefaultUni`: the universe continues to contain only types of ordinary constants. This
is important because encoding the family as an empty SOP or recursive structural type would expose
ordinary `case` or `unwrap` operations and break progress for the special runtime witness.

The retained constant is a canonical ByteString encoding a sorted non-empty table of constructor
tags and capture patterns. A capture pattern contains one byte per constructor field: zero skips
the field and one captures it. Its byte length therefore checks the exact constructor arity. The
checker and runtime share one decoder and reject any other selector value. There is no in-band
version byte: an incompatible format change requires a new builtin or language version.

## Erasure

```text
|BR_M(S)|                     = erased
|builtinrep MatchDataConstr b|      = constant b
|MatchDataConstr @S|                = force MatchDataConstr
```

Erasure is syntax directed. It neither inspects `S` nor manufactures `b`; the checked witness is
the sole source of retained runtime information. Consequently the old MatchDataConstr-specific type
application reification path is unnecessary.

## Semantic obligation

Define the validity relation:

```text
Valid_M(b, S)
  iff exists P.
       Decode(b) = P
    and ValidPattern(P)
    and Capt(P) = S
```

Witness typing establishes `Valid_M`. Soundness then needs one localized builtin lemma:

```text
Valid_M(b, S)    d in [[Data]]
-----------------------------------------------
matchDataConstrRuntime b d is in [[S]], or PLC errors
```

For MatchDataConstr this requires agreement between witness validation and runtime decoding, and that a
successful match constructs precisely the SOP branch and captured fields described by `Capt(P)`.
The existing PLC type-safety and erasure arguments otherwise remain ordinary.

This guarantee is about checked PLC. Raw UPLC has no static witness validation and may pass an
arbitrary constant, so the runtime implementation must remain total apart from the permitted PLC
error result and its cost model must cover rejected inputs as well as successful matches.

At the erased boundary there is no `BuiltinRep` type:

```text
PLC:   MatchDataConstr : forall S. BuiltinRep MatchDataConstr S -> Data -> S
UPLC:  force matchDataConstr #encoded-patterns data
```

The Haskell type-scheme wrapper for the first argument unlifts an ordinary ByteString, and its
execution-memory measure is exactly the standard ByteString measure. No representation-specific
builtin-universe or costing-wrapper type survives into UPLC.

## Serialization

The abstract family uses PLC type tag 8 and the witness uses PLC term tag 12. Since the previous
three-bit PLC type-tag space was full, typed PLC/PIR Flat encoding now uses four-bit type tags.
This changes typed serialization, but does not change UPLC serialization or the bytes submitted as
Cardano scripts: `TyBuiltinRep` is erased and the witness becomes an ordinary ByteString constant.

## References

- Crary, Weirich, and Morrisett, *Intensional Polymorphism in Type-Erasure Semantics*.
- Xi, Chen, and Chen, *Guarded Recursive Datatype Constructors*.
- Cheney and Hinze, *First-Class Phantom Types*.
