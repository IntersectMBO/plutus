# Checked builtin representations

Some polymorphic builtins need runtime information that determines the layout of their result.
That information must be an explicit term: deriving it from a type during erasure makes erasure
builtin-aware and is not ordinary representation passing.

`MatchData` uses the following type scheme:

```text
MatchData : forall S. BuiltinRep MatchData S -> Data -> S
```

`BuiltinRep MatchData S` is an abstract builtin type family. Its values are checked runtime
directives indexed by the type produced when the directive is interpreted. It follows the
representation-passing discipline of lambda-R: the type index is erased, while the runtime
representation is an ordinary explicitly passed term. Unlike lambda-R's singleton-like `R(S)`,
this family can have many operationally distinct inhabitants at one index, because different
matching patterns can capture the same result shape. Guarded recursive datatypes/GADTs and typed
format descriptions are therefore closer structural analogies.

## Static rules

Write `BR_M(S)` for `BuiltinRep MatchData S`, `Decode(b) = P` for decoding a representation
constant, and `Capt(P)` for the SOP type of the fields captured by `P`.

Formation is ordinary application of an abstract builtin type constructor:

```text
Gamma |- S : Type
-------------------------
Gamma |- BR_M(S) : Type
```

The only typed introduction form is a builtin-specific checked witness:

```text
b is a constant    Decode(b) = P    ValidPattern(P)
----------------------------------------------------
Gamma |- builtinrep MatchData b : BR_M(Capt(P))
```

The checker obtains this rule from the representation metadata associated with `MatchData`. The
metadata validates the constant and synthesizes its complete indexed type. Ordinary application
then requires that type to equal the instantiated argument type `BR_M(S)`. Other builtins cannot
claim the witness, and PLC has no eliminator for the abstract family.

The implementation represents `BR_M` as an uninhabited constructor in the builtin type universe.
This is important: encoding it as an empty SOP or recursive structural type would expose ordinary
`case` or `unwrap` operations and break progress for the special runtime witness.

## Erasure

```text
|BR_M(S)|                     = erased
|builtinrep MatchData b|      = constant b
|MatchData @S|                = force MatchData
```

Erasure is syntax directed. It neither inspects `S` nor manufactures `b`; the checked witness is
the sole source of retained runtime information. Consequently the old MatchData-specific type
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
matchDataRuntime b d is in [[S]], or PLC errors
```

For MatchData this requires agreement between witness validation and runtime decoding, and that a
successful match constructs precisely the SOP branch and captured fields described by `Capt(P)`.
The existing PLC type-safety and erasure arguments otherwise remain ordinary.

This guarantee is about checked PLC. Raw UPLC has no static witness validation and may pass an
arbitrary constant, so the runtime implementation must remain total apart from the permitted PLC
error result and its cost model must cover rejected inputs as well as successful matches.

## Serialization

The abstract family uses a new, append-only builtin-universe tag and the witness uses a previously
unused PLC term tag. Existing PLC type and term tags retain their encodings; in particular, adding
the family does not repurpose or widen the existing SOP type encoding.

## References

- Crary, Weirich, and Morrisett, *Intensional Polymorphism in Type-Erasure Semantics*.
- Xi, Chen, and Chen, *Guarded Recursive Datatype Constructors*.
- Cheney and Hinze, *First-Class Phantom Types*.
