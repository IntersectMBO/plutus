# CIP-57 constructor and field names in Plinth blueprints — design

**Date:** 2026-09-03
**Status:** approved design, not yet implemented
**Relation to other work:** independent of the UAL branch, but **blocks** the Lean
generator slice described in
`docs/superpowers/specs/2026-08-24-ual-extended-blueprints-design.md` §8.4.
Should land as its own PR.

## 1. The problem

A Plinth-generated `plutus.json` cannot express the names of a data type's
constructors or fields. A CIP-57 consumer that needs them — anything generating
typed code from the blueprint — cannot work from Plinth output, only from
Aiken's.

This is a **conformance gap, not a difference of convention**. CIP-57's own
normative example (`CIP-0057/README.md`, the `hello_world` blueprint) is:

```json
"schema": {
  "anyOf": [
    { "title": "Datum",
      "dataType": "constructor",
      "index": 0,
      "fields": [ { "title": "owner", "dataType": "bytes" } ] }
  ]
}
```

A per-field `title` is what the specification shows. Aiken emits it, and emits
per-constructor titles too — `cardano/address/Credential` in a real Aiken
blueprint gives `"title": "VerificationKey"` and `"title": "Script"` for its two
constructors.

### 1.1 Three distinct defects

**(a) No per-field name slot.** `PlutusTx.Blueprint.Schema` has

```haskell
data ConstructorSchema (referencedTypes :: [Type]) = MkConstructorSchema
  { index :: Natural
  , fieldSchemas :: [Schema referencedTypes]
  }
```

`fieldSchemas` is a bare list. There is no place to record that field 0 is called
`owner`.

**(b) A field's schema has nowhere to hold a name either.** Every field emitted
by `makeIsDataSchemaIndexed` is a `definitionRef`, i.e.

```haskell
  | SchemaDefinitionRef DefinitionId
```

— the one `Schema` constructor carrying **no `SchemaInfo`**. So even if
`fieldSchemas` held names, the existing per-schema annotation mechanism could not
supply them for the shape Plinth actually produces.

**(c) A constructor gets no name by default.** Verified against the repo's own
golden (`plutus-tx-plugin/test/Blueprint/Acme.golden.json`) before this change:
seven of its eight constructor schemas had no `title` at all. `Bool`, for
instance, was

```json
"Bool": { "oneOf": [
  { "dataType": "constructor", "fields": [], "index": 0 },
  { "dataType": "constructor", "fields": [], "index": 1 } ] }
```

so nothing distinguishes `False` from `True`. CIP-57 identifies a variant by its
`title`, and Aiken supplies one — `cardano/address/Credential` gives
`"title": "VerificationKey"` and `"title": "Script"`.

**An earlier draft of this spec misdiagnosed this defect**, claiming Plinth wrote
the *type* name into every constructor's `title` and the constructor name into
`description`. That was inferred from the one definition in the golden that does
carry titles, `Datum`, whose two variants are both `"title": "Datum"`. But that
comes from the test fixture's own explicit annotations —
`{-# ANN DatumLeft (SchemaTitle "Datum") #-}` in
`plutus-tx-plugin/test/Blueprint/Tests/Lib.hs:119` — an author's choice, not the
derivation's behaviour. The derivation supplied no title at all. `Datum` is
therefore expected to keep its titles unchanged after this work, because an
explicit annotation wins.

### 1.2 Why it matters concretely

`docs/superpowers/ual-linear-vesting-acceptance.md` traced this end to end. The
Lean side's `#import_blueprints` derives datum and redeemer *types* from CIP-57
`definitions`; `Formal/Vesting/Linear/Spec.lean` is built on the result
(`abbrev VestingDatum := LinearVesting.VestingDatum`, with fields `start_time`,
`end_time`, `recovery_time`). Given a Plinth blueprint it has no field names to
emit and no distinct constructor names, so substituting a Plinth `plutus.json`
for the Aiken one turns a Lean project that builds into one that does not.

Nothing about that reasoning is Lean-specific: any typed-code generator hits the
same wall.

## 2. The fix is cheap because the names are already in hand

`PlutusTx.Blueprint.TH.mkSchemaClause` already destructures
`TH.ConstructorInfo`:

```haskell
    mkSchemaConstructor (TH.ConstructorInfo {..}, info, naturalToInteger -> ctorIndex) = do
      fields <- for constructorFields $ \t -> [|definitionRef @($(pure t)) @($(pure ts))|]
```

`ConstructorInfo` carries `constructorName` and `constructorVariant`, and
`TH.RecordConstructor [Name]` gives a record's field names. This repo already
uses that pattern — `PlutusTx/AsData.hs:131` and `PlutusTx/Show/TH.hs:216` both
match on `TH.RecordConstructor`.

So **names require no new user annotation**: the TH derivation can populate them
from the Haskell declaration. Authors get correct blueprints without writing a
single `ANN` pragma. That is what makes this a fix rather than a project.

## 3. Design

### 3.1 Give fields a name

Add a field-schema wrapper to `PlutusTx.Blueprint.Schema`:

```haskell
-- | One field of a constructor: its schema, and its name where the source has one.
data FieldSchema (referencedTypes :: [Type]) = MkFieldSchema
  { fieldName :: Maybe Text
  -- ^ The record field's name. 'Nothing' for a positional constructor, which
  -- CIP-57 permits — the specification's per-field @title@ is optional.
  , fieldSchema :: Schema referencedTypes
  }
  deriving stock (Eq, Ord, Show, Generic, Data)
```

and change `ConstructorSchema`:

```haskell
  , fieldSchemas :: [FieldSchema referencedTypes]
```

Chosen over `[(Maybe Text, Schema referencedTypes)]` because the record's field
labels document the two positions at every use site, and over threading a
`SchemaInfo` because a field needs only a name — `description` and `comment` on a
field have no CIP-57 meaning distinct from the referenced definition's own.

**Rejected alternative: add `SchemaInfo` to `SchemaDefinitionRef`.** That would
let a `$ref` carry a title, but it conflates two things — the *referenced type's*
title and the *field's* name — and every other `$ref` use site would then have an
info slot it must ignore. The name belongs to the field, not to the reference.

### 3.2 Emit it

In `Schema`'s `ToJSON`:

```haskell
    SchemaConstructor info MkConstructorSchema {..} ->
      dataType info "constructor"
        & requiredField "index" index
        & requiredField "fields" fieldSchemas
        & Aeson.Object
```

`fieldSchemas` now needs its own `ToJSON`, which merges the name into the
field's schema object:

```haskell
instance ToJSON (FieldSchema referencedTypes) where
  toJSON MkFieldSchema {..} = case (fieldName, toJSON fieldSchema) of
    (Just n, Aeson.Object o) -> Aeson.Object (KeyMap.insert "title" (toJSON n) o)
    (_, v) -> v
```

Merging rather than nesting is what CIP-57 shows: the field object *is* the
schema object with a `title` added, not a wrapper around it. A field whose schema
does not serialise to an object (which cannot currently happen — every `Schema`
constructor produces one) falls through unchanged rather than silently dropping
the name.

`"title"` is already in `Pretty.keyOrder` in `PlutusTx.Blueprint.Write`
(`Write.hs:32`), so field objects order deterministically with no change there.

### 3.3 Populate it from the TH

In `mkSchemaConstructor`, pair each field type with its name:

```haskell
      let names = case constructorVariant of
            TH.RecordConstructor ns -> Just . nameBaseText <$> ns
            _ -> Nothing <$ constructorFields
      fields <- for (zip names constructorFields) $ \(n, t) ->
        [|MkFieldSchema $(TH.lift n) (definitionRef @($(pure t)) @($(pure ts)))|]
```

A `NormalConstructor` and an `InfixConstructor` yield `Nothing` for every field,
which is correct: those fields have no names to report, and CIP-57 makes the
per-field `title` optional.

### 3.4 Put the constructor name in `title`

Change `mkSchemaConstructor` so the `SchemaInfo` it emits per constructor
defaults its `title` to `constructorName`, rather than inheriting the type's
title. An explicit `{-# ANN Ctor (SchemaTitle "…") #-}` still wins.

**This is a behaviour change to existing output**, and the one part of this
design that is a judgement call rather than a conformance fix — CIP-57's example
has a single constructor whose name coincides with its type's, so it does not
discriminate. Two things settle it: Aiken's `Credential` shows constructor names
in `title`, and Plinth's current output makes a multi-constructor type's variants
indistinguishable, which is a defect on any reading.

`description` keeps whatever `SchemaDescription` says and is no longer
overloaded to carry the constructor name.

## 4. Scope

### 4.1 In scope

`FieldSchema` and the `ConstructorSchema` change; the `ToJSON` instances; the TH
population; the constructor-`title` change; regenerated goldens; a scriv
changelog fragment; and the documentation update of §4.3.

### 4.2 Out of scope

- Naming fields of types whose schema is hand-written rather than TH-derived. An
  author writing `instance HasBlueprintSchema T ts` by hand can supply
  `MkFieldSchema (Just "…")` themselves; nothing derives it for them.
- `AsData`-generated types (`PlutusTx.AsData`), unless they route through
  `makeIsDataSchemaIndexed`. Worth checking during implementation and recording
  either way.
- Any change to `SchemaDefinitionRef` (§3.1, rejected).

### 4.3 Breaking-change surface

`ConstructorSchema`'s `fieldSchemas` changes type, so any code constructing a
`ConstructorSchema` by hand breaks. Known sites:

- **`plutus-ledger-api` has seven hand-written sites**, and an earlier draft of
  this spec wrongly said there were none — that claim came from grepping only
  `plutus-tx` and `plutus-tx-plugin`. They are the `HasBlueprintSchema`
  instances for `Interval`, `LowerBound` and `UpperBound` in both
  `PlutusLedgerApi/V1/Interval.hs` and `PlutusLedgerApi/V1/Data/Interval.hs`,
  plus one in `PlutusLedgerApi/V4/Data/Time.hs` — 14 field references in total.
  Each is wrapped as `MkFieldSchema Nothing (…)`, preserving those types' output
  exactly. Giving them their real names (`Interval` is a record with
  `ivFrom`/`ivTo`) is a further improvement, deliberately out of scope per §4.2.
- `plutus-tx/test/Blueprint/Spec.hs` — hand-written instances too, but every one
  returns `SchemaBuiltInUnit emptySchemaInfo`, so none touches
  `ConstructorSchema`.
- Anything outside this repo doing the same. This is public API, so the
  changelog fragment must say so plainly.

JSON output changes for every TH-derived sum or record type, so these need
regenerating and **reading**:

- `plutus-tx-plugin/test/Blueprint/Acme.golden.json`
- `doc/docusaurus/static/plutus.json`
- the UAL goldens under `plutus-tx/test/Ual/Golden/` are **unaffected**:
  `grep constructor` over them finds nothing, because the fixtures use `Integer`,
  `[Integer]` and `BuiltinData`

Documentation to update: `doc/docusaurus/docs/working-with-scripts/producing-a-blueprint.md`
documents `SchemaTitle`/`SchemaDescription` on constructors; §3.4 changes what
those do relative to the default, and the page should say that field names come
from the Haskell record automatically.

## 5. Testing

- A golden covering a **record** constructor with named fields, and a
  **multi-constructor** type where the variants must be distinguishable by
  `title`. `Acme.golden.json` already has `Datum` (two constructors, one with a
  payload) and `DatumPayload` — extend rather than invent, and read the diff.
- A golden covering a **positional** constructor, asserting fields carry no
  `title` rather than an empty one.
- Validate a regenerated blueprint against the CIP-57 meta-schema at
  `CIP-0057/schemas/` (a different git repo — do not commit there). Two
  practical notes from doing it: the schemas' `$id`s are absolute
  `https://cips.cardano.org/…` URIs whose published copies **404**, so the
  relative `$ref`s must be resolved from a local store rather than fetched
  (`check-jsonschema` cannot; `jsonschema`'s `RefResolver` with a `store=` map
  can); and **the result barely bears on this change**. A negative control
  setting a field's `title` to the integer `123` also validates, because
  `$defs/constructor` in `plutus-data.json` constrains only `dataType`, `index`
  and `fields`, has no `additionalProperties: false`, and does not mention
  `title` at all. Treat the pass as a regression check that conformance was not
  broken — not as evidence the feature is right. A control that drops the
  required `preamble` does fail, which is what shows the validator is working.
- **The acceptance test that matters — done, and it passes.** The Lean consumer
  reads exactly the key this change adds: `Basic.lean:205` is
  `let ftitle := getOptStr f "title"`, and `emitStructType` (`:584`) bails with
  *"has positional (unnamed) fields; no Lean type emitted (the slot stays raw
  Data)"* unless **every** field has one. Against the regenerated
  `Acme.golden.json`, `Params` (6 named fields), `DatumPayload` and `Datum2` now
  satisfy that and would emit Lean records where before they degraded to raw
  `Data`; `Param2a`/`Param2b` still skip, correctly, being genuinely positional
  in Haskell. Verified by reading both sides and matching keys — **no Lean
  toolchain was available here, so this is not a claim that the Lean project
  builds.**

## 6. Open questions

Answered by implementing:

- **`PlutusTx.AsData`-generated types.** `PlutusTx/AsData.hs` matches on
  `TH.RecordConstructor` already (`:131`) but generates `ToData`/`FromData`
  through `makeIsDataIndexed`, not `makeIsDataSchemaIndexed`, so it produces no
  `HasBlueprintSchema` instance and no constructor schema. An `AsData` type that
  also wants a blueprint schema gets one the usual way, and then picks up field
  names like any other record. Nothing to do.
- **Whether any consumer depended on the old constructor `title`.** It could not
  have: the derivation supplied none. The only titles in the repo's blueprints
  came from explicit annotations, which are unchanged.

Found while implementing, and worth fixing separately:

- **`plutus-tx/test/Blueprint/Definition/Spec.hs` is weaker than it reads.** Its
  `universe` call is at type `[SomeSchema] -> [[SomeSchema]]`, using lens's
  `Plated [a]` instance, so it walks the list spine and never descends into a
  `Schema`. It therefore only sees definition refs that are a definition's
  top-level schema. Neither caused nor fixed by this change; the `Plated (Schema
  …)` instance it imports is effectively unused.
- **A definition's `title` is neither a usable identifier nor unique**, and a
  generator naming types from it must sanitise and disambiguate. This is not
  introduced here — every case below comes from an explicit `SchemaTitle`
  annotation or a hand-written schema, which this design deliberately leaves
  untouched — but it is on the same path as the constructor-title decision, so it
  belongs recorded next to it. Audited across both regenerated blueprints:

  | Definition | `title` | Source |
  |---|---|---|
  | `LowerBound_Extended_Integer`, `LowerBound_Extended_POSIXTime` | `LowerBound` | hand-written `plutus-ledger-api` instance |
  | `UpperBound_Extended_Integer`, `UpperBound_Extended_POSIXTime` | `UpperBound` | same |
  | `Rational` | `(,)` | tuple constructor |
  | `MyParams` | `Title for the MyParams definition` | `SchemaTitle` in the docs example |
  | `Bytes_Void` | `SchemaBytes` | test fixture |

  The `LowerBound`/`UpperBound` pairs are the sharp case: two distinct types
  collide on one name, so `PlutusCore/UPLC/BlueprintEncoding/Basic.lean`'s
  `defTypeName` would emit one Lean type for both instantiations. `Rational`
  becoming `(,)` is not a legal Lean identifier at all.

- **A single-constructor type deliberately carries no constructor title.** Its
  definition object *is* the constructor schema, so a title there is what
  `defTypeName` reads as the *type's* name — and the constructor's name would
  displace the more useful one (`VestingParams` became `MkVestingParams` in a
  first attempt). CIP-0057's own example agrees: the single constructor of
  `Datum` is titled `Datum`. Pinned by the test "a single-constructor type
  carries no constructor title"; without it the unconditional default could be
  restored with no test objecting.
- **The hand-written `plutus-ledger-api` instances could carry real field
  names.** `Interval` is a record with `ivFrom`/`ivTo`; its schema currently
  reports `MkFieldSchema Nothing`. Out of scope per §4.2, but it is exactly the
  kind of type a Lean generator will meet.
