# ADR 6: `Term` with type information

Date: 2022-12

## Authors

Marty Stumpf <marty.stumpf@iohk.io>

## Status

Proposed

## Context

We are exploring various ways to increase script capacity and efficiency
(see [PLT-1044](https://input-output.atlassian.net/browse/PLT-1044)).
E.g., inlining saturated functions. See also ADR 5. It's a complex issue but type information can help.
If we have the type information it can open up other ways we can improve efficiency.

Currently, we don't have terms that are annotated with type information after they are typechecked.
This ADR describes an implementation to add that without disrupting a large portion of the codebase.

## Decision

### Adding a term type with type information

Currently, we have one type of terms for each PIR, PLC, and UPLC,
and the terms don't carry type information from the type checker.
E.g., our PIR [Term](https://github.com/input-output-hk/plutus/blob/06c5831ea5934beef2f4c4178a8c53771381f1bf/plutus-core/plutus-ir/src/PlutusIR/Core/Type.hs#L117) is:

```haskell
-- current PIR terms
data Term tyname name uni fun a =
                        -- Plutus Core (ish) forms, see note [Declarations in Plutus Core]
                          Let a Recursivity (NonEmpty (Binding tyname name uni fun a)) (Term tyname name uni fun a)
                        | Var a name
                        | TyAbs a tyname (Kind a) (Term tyname name uni fun a)
                        | LamAbs a name (Type tyname uni a) (Term tyname name uni fun a)
                        | Apply a (Term tyname name uni fun a) (Term tyname name uni fun a)
                        | Constant a (PLC.Some (PLC.ValueOf uni))
                        | Builtin a fun
                        | TyInst a (Term tyname name uni fun a) (Type tyname uni a)
                        | Error a (Type tyname uni a)
                        | IWrap a (Type tyname uni a) (Type tyname uni a) (Term tyname name uni fun a)
                        | Unwrap a (Term tyname name uni fun a)
                        deriving stock (Functor, Show, Generic)
```

We proposed to add a term type that is distinguished from the current type in that it carries [
type](https://github.com/input-output-hk/plutus/blob/06c5831ea5934beef2f4c4178a8c53771381f1bf/plutus-core/plutus-core/src/PlutusCore/Core/Type.hs#L93)
information.
The proposed term types include a generic term type,
a term type with type information, and a term type without type information (what we have currently).

```haskell
-- the new generic term: it has an additional parameter: tyinfo
data GenericTerm tyinfo tyname name uni fun a =
    Let tyinfo a Recursivity (NonEmpty (Binding tyname name uni fun a)) (Term tyname name uni fun a)
    | Var tyinfo a name
    | TyAbs tyinfo a tyname (Kind a) (Term tyname name uni fun a)
    | LamAbs tyinfo a name (Type tyname uni a) (Term tyname name uni fun a)
    | Apply tyinfo a (Term tyname name uni fun a) (Term tyname name uni fun a)
    | Constant tyinfo a (PLC.Some (PLC.ValueOf uni))
    | Builtin tyinfo a fun
    | TyInst tyinfo a (Term tyname name uni fun a) (Type tyname uni a)
    | Error tyinfo a (Type tyname uni a)
    | IWrap tyinfo a (Type tyname uni a) (Type tyname uni a) (Term tyname name uni fun a)
    | Unwrap tyinfo a (Term tyname name uni fun a)
    deriving stock (Functor, Show, Generic)

-- the new term type that is similar to our current implementation, with tyinfo set to ()
type Term = GenericTerm () tyname name uni fun a

-- the new term type that has type information
type TermWithTypeInfo = GenericTerm (Type tyname uni ann) tyname name uni fun a
```

### Using the `PatternSynonyms` pragma to minimize code change

Using the `PatternSynonyms` extension, we can now add these synonyms so that all existing
code that pattern matches on the terms work:

```haskell
pattern Let = Let ()
pattern Var = Var ()
pattern TyAbs = TyAbs ()
...
```

### Using the type checker to generate the type information

Now that we have a type of terms with type information, the type checker can return a `TermWithTypeInfo` so that we can utilize these for our optimization passes.

## Conclusion

This proposal is still a significant change to our codebase. However, it's benefit may outweigh the cost. Script capacity and efficiency is important and having type information can expand and improve optimizations we can do.
