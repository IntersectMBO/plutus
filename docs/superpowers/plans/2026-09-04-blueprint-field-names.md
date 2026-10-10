# CIP-57 Constructor and Field Names Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make Plinth-generated CIP-57 blueprints carry the names of a data type's constructors and record fields, so a consumer can generate typed code from them.

**Architecture:** Add a `FieldSchema` wrapper holding an optional field name beside a field's schema, change `ConstructorSchema.fieldSchemas` to use it, merge the name into the field's JSON object as `title`, and populate it in the Template Haskell derivation from `ConstructorInfo`'s `RecordConstructor` variant — so authors need no new annotation. Separately, default each constructor's `title` to the constructor's own name instead of the type's.

**Tech Stack:** Haskell (GHC 9.6.7), `aeson`, `th-abstraction`, `tasty` + `tasty-hunit`, golden files via `Test.Tasty.Extras`.

**Spec:** `docs/superpowers/specs/2026-09-03-blueprint-field-names-design.md`

---

## Orientation for the implementer

You are in the `plutus` monorepo (IntersectMBO/plutus), branch `feat/ual-extended-blueprints`.

### Environment — every command needs the nix devshell

`nix` is available but NOT on `PATH` in a non-interactive shell. Run everything from `/Users/romainsoulat/plutus` as:

```bash
export PATH="/nix/var/nix/profiles/default/bin:$PATH"
nix develop --accept-flake-config --command bash -c '<command>'
```

That gives GHC 9.6.7 (the repo's primary supported version), cabal 3.12.1 and `fourmolu` 0.17. Use the root `cabal.project`; there is no `--project-file` flag.

- `plutus-tx` tests: `cabal test plutus-tx:plutus-tx-test` — **baseline 304 passing**
- plugin tests (where the blueprint golden lives): `cabal test plutus-tx-plugin:plutus-tx-plugin-tests --test-options="-p Blueprint"`
- **Never `cabal run` from the repo root** — it writes a stray duplicate golden tree at `<repo-root>/test/`, because golden paths resolve relative to cwd. Use `cabal test`, or `cabal test --test-options="-p /pattern/"`.
- **Run `fourmolu --mode check` as its own step and read its result.** Note that `fourmolu … && echo ok` on one line does NOT gate a command on the next line — that mistake has already produced a falsely-clean report in this repo's history.
- **Commit inside the devshell and let the pre-commit hooks run** (cabal-fmt, editorconfig-checker, fourmolu). Do NOT pass `--no-verify`.

### Conventions

- `plutus-tx` uses `NoImplicitPrelude`; modules under `src/` must `import Prelude`.
- `plutus-tx`'s library sets `default-extensions: Strict`, so **all data fields are strict**. A record holding `error "…"` in any field is bottom *as a whole*; reading any other field throws. If you need a partial default, you need a lazy field annotation (`~`).
- `-Wall` with `-Werror` in CI, plus `-Wunused-packages`. No unused imports or dependencies.
- Single-constructor records take the `Mk` prefix (`MkFieldSchema`); type names stay bare.
- `.editorconfig` sets `max_line_length = 100`; `fourmolu.yaml` sets `column-limit: 100`.
- **Comments must not claim more than the code does.** This was the single most common review finding on the preceding piece of work. If your implementation has a limitation, state it beside the code.

### Facts about the files you are changing, already verified

- **`plutus-tx/src/PlutusTx/Blueprint/Schema.hs` has no export list** (`module PlutusTx.Blueprint.Schema where`), so adding a type needs no export change.
- **`Schema` derives `Plated` via `deriving anyclass`**, at `Schema.hs:63`:
  ```haskell
  deriving anyclass instance Typeable referencedTypes => Plated (Schema referencedTypes)
  ```
  `Plated`'s default method is `Data`-based, so `FieldSchema` **must derive `Data`** or this instance stops compiling.
- **`withSchemaInfo` (`Schema.hs:145`) does not touch `fieldSchemas`** — it only maps over the `SchemaInfo` of each constructor. No change needed there.
- **`"title"` is already in `Pretty.keyOrder`** (`PlutusTx/Blueprint/Write.hs:32`), so field objects order deterministically with no change there.
- **No in-repo site constructs a `ConstructorSchema` by hand.** The hand-written `HasBlueprintSchema` instances in `plutus-tx/test/Blueprint/Spec.hs` all return `SchemaBuiltInUnit emptySchemaInfo`. Only the TH derivation builds one.
- **The UAL goldens under `plutus-tx/test/Ual/Golden/` are unaffected** — their fixtures use `Integer`, `[Integer]` and `BuiltinData`, none of which produces a constructor schema. `grep constructor` over them finds nothing.
- **One blueprint golden exists**: `plutus-tx-plugin/test/Blueprint/Acme.golden.json`. `doc/docusaurus/static/plutus.json` is also generated output that will change.

### One trap specific to this change

`plutus-tx/test/Blueprint/Definition/Spec.hs:55-61` looks like it walks nested schemas:

```haskell
    referencedIds =
      Set.fromList
        [ ref
        | schemas <- universe (Map.elems definitions)
        , SomeSchema (SchemaDefinitionRef ref) <- schemas
        ]
```

It does **not**. `universe` there is at type `[SomeSchema] -> [[SomeSchema]]`, using lens's `Plated [a]` instance, which walks the *list spine* and yields suffixes — it never descends into a `Schema`. So the test only sees definition refs that are the top-level schema of a definition. Your change moves refs one layer deeper (inside a `FieldSchema`), which this test would not have noticed either way. **Do not "fix" that test as part of this task** — but Task 5 records it, because it means the test is weaker than it reads.

## File structure

**Modified:**

| File | Change |
|---|---|
| `plutus-tx/src/PlutusTx/Blueprint/Schema.hs` | Add `FieldSchema` + its `ToJSON`; change `ConstructorSchema.fieldSchemas`; extend `SchemaConstructor`'s `ToJSON` |
| `plutus-tx/src/PlutusTx/Blueprint/TH.hs` | Populate field names and the constructor `title` in `mkSchemaConstructor` |
| `plutus-tx-plugin/test/Blueprint/Acme.golden.json` | Regenerated |
| `doc/docusaurus/static/plutus.json` | Regenerated |
| `doc/docusaurus/docs/working-with-scripts/producing-a-blueprint.md` | Document automatic field names and the constructor-`title` default |
| `plutus-tx/changelog.d/20260904_000000_blueprint_field_names.md` | New scriv fragment |

**New tests:**

| File | Responsibility |
|---|---|
| `plutus-tx/test/Blueprint/FieldNames/Spec.hs` | A record type, a multi-constructor type, and a positional constructor — asserting on the emitted JSON |
| `plutus-tx/test/Blueprint/FieldNames/Golden/field-names.golden.json` | Its golden |

Tests go in `plutus-tx` rather than `plutus-tx-plugin` because nothing here needs the plugin — `makeIsDataSchemaIndexed` is plain TH.

---

### Task 1: `FieldSchema` and its JSON

**Files:**
- Modify: `plutus-tx/src/PlutusTx/Blueprint/Schema.hs`
- Create: `plutus-tx/test/Blueprint/FieldNames/Spec.hs`
- Modify: `plutus-tx/test/Spec.hs`, `plutus-tx/plutus-tx.cabal`

This task adds the type and its encoding, and drives it from a **hand-written** `ConstructorSchema` so the encoding is pinned independently of the TH. Task 2 makes the TH produce them.

- [ ] **Step 1: Write the failing test**

Create `plutus-tx/test/Blueprint/FieldNames/Spec.hs`:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Blueprint.FieldNames.Spec (tests) where

import Prelude

import Data.Aeson (Value, toJSON)
import Data.Aeson qualified as Aeson
import PlutusTx.Blueprint.Schema
  ( ConstructorSchema (..)
  , FieldSchema (..)
  , Schema (..)
  , emptyBytesSchema
  )
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests =
  testGroup
    "field names"
    [ testCase "a named field carries its name as title" $
        toJSON (namedCtor :: Schema '[])
          @?= Aeson.object
            [ "dataType" Aeson..= ("constructor" :: String)
            , "index" Aeson..= (0 :: Int)
            , "fields"
                Aeson..= [ Aeson.object
                             [ "title" Aeson..= ("owner" :: String)
                             , "dataType" Aeson..= ("bytes" :: String)
                             ]
                         ]
            ]
    , testCase "an unnamed field emits no title" $
        fieldsOf (toJSON (positionalCtor :: Schema '[]))
          @?= Just [Aeson.object ["dataType" Aeson..= ("bytes" :: String)]]
    ]

-- | @{ "title": "owner", "dataType": "bytes" }@ — a record field.
namedCtor :: Schema referencedTypes
namedCtor =
  SchemaConstructor
    emptySchemaInfo
    (MkConstructorSchema 0 [MkFieldSchema (Just "owner") bytes])

-- | The same constructor with a positional field.
positionalCtor :: Schema referencedTypes
positionalCtor =
  SchemaConstructor
    emptySchemaInfo
    (MkConstructorSchema 0 [MkFieldSchema Nothing bytes])

bytes :: Schema referencedTypes
bytes = SchemaBytes emptySchemaInfo emptyBytesSchema

-- | Project the @fields@ array, so a test can assert on it alone.
fieldsOf :: Value -> Maybe [Value]
fieldsOf v = case v of
  Aeson.Object o -> case Aeson.lookup "fields" o of
    Just (Aeson.Array a) -> Just (foldr (:) [] a)
    _ -> Nothing
  _ -> Nothing
```

`Aeson.lookup` is `Data.Aeson.KeyMap.lookup`; if the unqualified name does not resolve, add `import Data.Aeson.KeyMap qualified as KeyMap` and use `KeyMap.lookup`. `emptyBytesSchema` does exist — `Schema.hs:201` defines it as `MkBytesSchema {enum = [], minLength = Nothing, maxLength = Nothing}`.

Wire it in. In `plutus-tx/test/Spec.hs`, add next to the other qualified test imports:

```haskell
import Blueprint.FieldNames.Spec qualified
```

and add `Blueprint.FieldNames.Spec.tests` to the `tests` list. In `plutus-tx/plutus-tx.cabal`, add `Blueprint.FieldNames.Spec` to the test suite's `other-modules`, alphabetically (it sorts after `Blueprint.Definition.Spec` and before `Blueprint.Spec`).

- [ ] **Step 2: Run to verify it fails**

Run:
```bash
export PATH="/nix/var/nix/profiles/default/bin:$PATH"
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test'
```
Expected: build failure, `Module 'PlutusTx.Blueprint.Schema' does not export 'FieldSchema'`.

- [ ] **Step 3: Add the type**

In `plutus-tx/src/PlutusTx/Blueprint/Schema.hs`, add immediately before `ConstructorSchema`:

```haskell
{-| One field of a constructor: its schema, plus its name where the source has
one.

CIP-0057 gives each field object an optional @title@ — see the @hello_world@
blueprint in the specification, whose single field is
@{ "title": "owner", "dataType": "bytes" }@. A positional constructor has no
names to report, hence 'Maybe'. -}
data FieldSchema (referencedTypes :: [Type]) = MkFieldSchema
  { fieldName :: Maybe Text
  , fieldSchema :: Schema referencedTypes
  }
  deriving stock (Eq, Ord, Show, Generic, Data)

{-| The field name is merged into the field's own schema object rather than
wrapping it, which is the shape CIP-0057 shows: a field object *is* a schema
object with a @title@ added.

A schema that did not serialise to a JSON object would lose its name here. No
'Schema' constructor does that today — every branch of the instance below
produces an object — and the fallthrough drops the name rather than emitting a
malformed field. -}
instance ToJSON (FieldSchema referencedTypes) where
  toJSON MkFieldSchema {fieldName, fieldSchema} =
    case (fieldName, toJSON fieldSchema) of
      (Just n, Aeson.Object o) -> Aeson.Object (KeyMap.insert "title" (toJSON n) o)
      (_, v) -> v
```

`Data`, `Generic`, `Text`, `KeyMap` and `Aeson` are all already imported by this module — check the import list rather than adding duplicates. `Data` in particular is **required**: `Schema`'s `Plated` instance at line 63 is `deriving anyclass`, whose default method is `Data`-based, and it will stop compiling without it.

Then change `ConstructorSchema`:

```haskell
data ConstructorSchema (referencedTypes :: [Type]) = MkConstructorSchema
  { index :: Natural
  -- ^ Constructor index
  , fieldSchemas :: [FieldSchema referencedTypes]
  -- ^ Field schemas, in declaration order
  }
  deriving stock (Eq, Ord, Show, Generic, Data)
```

The `SchemaConstructor` branch of `Schema`'s `ToJSON` needs no edit — `requiredField "fields" fieldSchemas` now picks up the new element instance. Confirm that by reading it rather than assuming.

- [ ] **Step 4: Run to verify it passes**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test'
```
Expected: 306 passing (304 baseline + 2).

If the `Plated` instance fails to compile, `FieldSchema` is missing `Data`.

- [ ] **Step 5: Check formatting, as its own step**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'fourmolu --mode check plutus-tx/src/PlutusTx/Blueprint/Schema.hs plutus-tx/test/Blueprint/FieldNames/Spec.hs'
```
Expected: exit 0, no output. If it reports a difference, run `--mode inplace` and re-run the tests.

- [ ] **Step 6: Commit**

```bash
nix develop --accept-flake-config --command bash -c 'git add plutus-tx && git commit -m "feat(plutus-tx): give constructor fields an optional CIP-57 title

CIP-0057 gives each field object an optional title; ConstructorSchema had
nowhere to hold one. FieldSchema adds it, merged into the field schema
object rather than wrapping it, which is the shape the specification shows."'
```

---

### Task 2: Populate field names from the Template Haskell

**Files:**
- Modify: `plutus-tx/src/PlutusTx/Blueprint/TH.hs`
- Modify: `plutus-tx/test/Blueprint/FieldNames/Spec.hs`

- [ ] **Step 1: Write the failing test**

Add to `plutus-tx/test/Blueprint/FieldNames/Spec.hs`. Extend the pragmas with `{-# LANGUAGE DeriveAnyClass #-}`, `{-# LANGUAGE DerivingStrategies #-}`, `{-# LANGUAGE TemplateHaskell #-}` and `{-# LANGUAGE TypeApplications #-}`, and the imports with:

```haskell
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (schema))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
```

Then the fixture and its tests:

```haskell
-- | A record, so its fields have names to report.
data Escrow = MkEscrow
  { escrowOwner :: Integer
  , escrowDeadline :: Integer
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Escrow [('MkEscrow, 0)])

-- | A positional constructor, so its fields have none.
data Pair = MkPair Integer Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Pair [('MkPair, 0)])
```

and add these two cases to the `tests` list:

```haskell
    , testCase "a derived record's fields carry their Haskell names" $
        (fmap titleOf <$> fieldsOf (toJSON (schema @Escrow @'[Escrow, Integer])))
          @?= Just [Just "escrowOwner", Just "escrowDeadline"]
    , testCase "a derived positional constructor's fields carry no names" $
        (fmap titleOf <$> fieldsOf (toJSON (schema @Pair @'[Pair, Integer])))
          @?= Just [Nothing, Nothing]
```

with the helper:

```haskell
-- | The @title@ of a field object, if it has one.
titleOf :: Value -> Maybe String
titleOf v = case v of
  Aeson.Object o -> case Aeson.lookup "title" o of
    Just (Aeson.String t) -> Just (show t)
    _ -> Nothing
  _ -> Nothing
```

`show` on a `Text` adds quotes, so compare against `Just "\"escrowOwner\""` or convert with `Data.Text.unpack` — pick one and make the expectation match. Prefer `Text.unpack`, and add `import Data.Text qualified as Text`.

The `@'[Escrow, Integer]` type application must list every type the schema references, or `HasSchemaDefinition` will not resolve. If it complains, add the missing type to the list; `plutus-tx/test/Blueprint/Spec.hs` shows the pattern.

- [ ] **Step 2: Run to verify it fails**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test --test-options="-p /field names/"'
```
Expected: the two new cases FAIL with `Just [Nothing,Nothing]` where names were expected — the TH does not populate them yet. The positional case passes already, which is correct: it is a guard against the change over-reaching.

- [ ] **Step 3: Populate the names**

In `plutus-tx/src/PlutusTx/Blueprint/TH.hs`, replace `mkSchemaConstructor`:

```haskell
    mkSchemaConstructor :: (TH.ConstructorInfo, SchemaInfo, Natural) -> TH.ExpQ
    mkSchemaConstructor (TH.ConstructorInfo {..}, info, naturalToInteger -> ctorIndex) = do
      {- A record constructor knows its field names; a normal or infix one has
      none to report, and CIP-0057 makes the per-field title optional. -}
      let names = case constructorVariant of
            TH.RecordConstructor fieldNames -> Just . TH.nameBase <$> fieldNames
            _ -> Nothing <$ constructorFields
      fields <- for (zip names constructorFields) $ \(name, t) ->
        [|
          MkFieldSchema
            (Text.pack <$> name)
            (definitionRef @($(pure t)) @($(pure ts)))
          |]
      [|SchemaConstructor info (MkConstructorSchema ctorIndex $(pure (TH.ListE fields)))|]
```

Add `FieldSchema (..)` to the `PlutusTx.Blueprint.Schema` import at line 31:

```haskell
import PlutusTx.Blueprint.Schema (ConstructorSchema (..), FieldSchema (..), Schema (..))
```

`Data.Text qualified as Text` and `for` are already imported. `TH.nameBase` returns a `String`; `Text.pack <$> name` lifts it into the `Maybe`. `zip` truncating to the shorter list is safe here because `RecordConstructor`'s name list and `constructorFields` are the same length by construction — a record has exactly one name per field.

If the splice fails to compile because `name :: Maybe String` cannot be lifted, note that `Lift (Maybe String)` exists, so the likelier cause is a missing `TH.lift`; wrap it as `$(TH.lift name)` in place of the bare `name`.

- [ ] **Step 4: Run to verify it passes**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test --test-options="-p /field names/"'
```
Expected: 4 passing.

Then the whole suite:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test'
```
Expected: 308 passing (304 + 4). Any *other* test that now fails is a real regression — investigate rather than accepting it.

- [ ] **Step 5: Check formatting**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'fourmolu --mode check plutus-tx/src/PlutusTx/Blueprint/TH.hs plutus-tx/test/Blueprint/FieldNames/Spec.hs'
```
Expected: exit 0.

- [ ] **Step 6: Commit**

```bash
nix develop --accept-flake-config --command bash -c 'git add plutus-tx && git commit -m "feat(plutus-tx): derive CIP-57 field names from record constructors

ConstructorInfo already carries the field names, so a record type gets
conformant field titles with no annotation from the author. A positional
constructor reports none, which CIP-0057 permits."'
```

---

### Task 3: Put the constructor name in `title`

**Files:**
- Modify: `plutus-tx/src/PlutusTx/Blueprint/TH.hs`
- Modify: `plutus-tx/test/Blueprint/FieldNames/Spec.hs`

Today Plinth writes the *type* name into every constructor's `title` and the *constructor* name into `description`, so a sum type's variants are indistinguishable by title. Aiken writes the constructor name. This step changes the default; an explicit `{-# ANN Ctor (SchemaTitle "…") #-}` must still win.

**This changes existing output**, and is the one part of this work that is a judgement call rather than a conformance fix — CIP-57's own example has a single constructor whose name coincides with its type's, so it does not discriminate.

- [ ] **Step 1: Write the failing test**

Add to `plutus-tx/test/Blueprint/FieldNames/Spec.hs` a two-constructor fixture:

```haskell
-- | Two constructors, so their titles must distinguish them.
data Outcome = Accepted | Rejected
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Outcome [('Accepted, 0), ('Rejected, 1)])
```

and this case, plus the helper it needs:

```haskell
    , testCase "each constructor's title is its own name" $
        variantTitles (toJSON (schema @Outcome @'[Outcome]))
          @?= Just [Just "Accepted", Just "Rejected"]
```

```haskell
{-| The @title@ of each variant of a @oneOf@ schema. -}
variantTitles :: Value -> Maybe [Maybe String]
variantTitles v = case v of
  Aeson.Object o -> case Aeson.lookup "oneOf" o of
    Just (Aeson.Array a) -> Just (fmap titleOf (foldr (:) [] a))
    _ -> Nothing
  _ -> Nothing
```

- [ ] **Step 2: Run to verify it fails**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test --test-options="-p /constructor/"'
```
Expected: FAIL. With no `ANN` pragmas on `Outcome`, today's output has no titles at all, so expect `Just [Nothing,Nothing]`.

- [ ] **Step 3: Default the constructor title**

In `mkSchemaConstructor`, default the `SchemaInfo`'s `title` to the constructor's name when the author supplied none. `SchemaInfo` is `MkSchemaInfo { title, description, comment :: Maybe String }` from `PlutusTx.Blueprint.Schema.Annotation`. Insert before the `let names = …` line:

```haskell
      {- CIP-0057 identifies a variant by its title. The type's own title would
      make every variant of a sum type identical, so default to the
      constructor's name; an explicit SchemaTitle annotation still wins. -}
      let info' = info {title = Just (TH.nameBase constructorName)}
          ctorInfo = case title info of
            Just _ -> info
            Nothing -> info'
```

and use `ctorInfo` in place of `info` in the final quotation:

```haskell
      [|SchemaConstructor ctorInfo (MkConstructorSchema ctorIndex $(pure (TH.ListE fields)))|]
```

`title` is a field selector on `SchemaInfo` and is already imported by `TH.hs` via the `PlutusTx.Blueprint.Schema.Annotation` import — check whether it is imported unqualified, and if the record-update syntax collides with another `title` in scope (`deriveParameterBlueprint` binds a local `title`), rename the local binding rather than qualifying, or use `NamedFieldPuns`-free explicit construction:

```haskell
          ctorInfo = case title info of
            Just _ -> info
            Nothing -> MkSchemaInfo (Just (TH.nameBase constructorName)) (description info) (comment info)
```

Prefer whichever compiles with no ambiguity, and say in your report which you used.

- [ ] **Step 4: Run to verify it passes**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test'
```
Expected: 309 passing (304 + 5).

**The plugin's blueprint golden will now differ.** Run it and expect a FAILURE with a diff, which is the point:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx-plugin:plutus-tx-plugin-tests --test-options="-p Blueprint"'
```
Do not accept that golden yet — Task 4 does it, after you have read it.

- [ ] **Step 5: Commit**

```bash
nix develop --accept-flake-config --command bash -c 'fourmolu --mode check plutus-tx/src/PlutusTx/Blueprint/TH.hs plutus-tx/test/Blueprint/FieldNames/Spec.hs'
nix develop --accept-flake-config --command bash -c 'git add plutus-tx && git commit -m "feat(plutus-tx): default a constructor title to the constructor name

The type name made every variant of a sum type identical by title, which is
what CIP-0057 identifies a variant by. An explicit SchemaTitle annotation
still wins. The plugin blueprint golden changes as a result."'
```

---

### Task 4: Regenerate and read the affected output

**Files:**
- Modify: `plutus-tx-plugin/test/Blueprint/Acme.golden.json`
- Modify: `doc/docusaurus/static/plutus.json`
- Create: `plutus-tx/test/Blueprint/FieldNames/Golden/field-names.golden.json`

A golden nobody read is worse than no test. Each step here ends in you reporting what the diff actually says.

- [ ] **Step 1: Regenerate the plugin's blueprint golden**

Run:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx-plugin:plutus-tx-plugin-tests --test-options="-p Blueprint --accept"'
```

Then read the diff:
```bash
git diff plutus-tx-plugin/test/Blueprint/Acme.golden.json
```

**Check three things and report them:**
1. `Datum`'s two variants now have distinct titles (`DatumLeft`, `DatumRight`) instead of both being `"title": "Datum"`.
2. `DatumPayload`'s fields carry their Haskell record names as `title`.
3. `Bool`'s two constructors now have titles where before they had none.

If any of those is absent, stop — the change is not doing what it should, and accepting the golden would cement it.

- [ ] **Step 2: Regenerate the docs blueprint**

The `example-cip57` executable writes it. Build and run it from a scratch directory, **not** `cabal run`:

```bash
nix develop --accept-flake-config --command bash -c 'cabal build example-cip57'
nix develop --accept-flake-config --command bash -c 'BIN=$(cabal list-bin example-cip57) && cd /private/tmp/claude-501/-Users-romainsoulat-plutus/0153dc76-d923-4759-8742-351766f3eba8/scratchpad && "$BIN"'
```

Find where it wrote `plutus.json`, compare against `doc/docusaurus/static/plutus.json`, and copy it over if the only differences are the new titles. Read the diff and report it. If the executable resolves its output path via `getDataFileName` and writes into the repo, clean up any stray file.

- [ ] **Step 3: Add the field-names golden**

The unit tests in Task 1–3 assert on projections. Add one golden over a full schema so the whole object shape is pinned. In `plutus-tx/test/Blueprint/FieldNames/Spec.hs`, add:

```haskell
    , goldenVsText
        "escrow schema"
        "test/Blueprint/FieldNames/Golden/field-names.golden.json"
        ( Text.decodeUtf8
            ( LBS.toStrict
                (Aeson.encode (toJSON (schema @Escrow @'[Escrow, Integer])))
            )
        )
```

with `import Data.ByteString.Lazy qualified as LBS`, `import Data.Text.Encoding qualified as Text` and `import Test.Tasty.Extras (goldenVsText)`. Note you will then have two modules aliased `Text` if you also imported `Data.Text qualified as Text` in Task 2 — that is legal in Haskell as long as each used name is unambiguous, but prefer distinct aliases (`Text` and `TextEnc`) for readability.

Run the suite, then **open the created golden and paste its content into your report**. Confirm it shows `"title": "escrowOwner"` and `"title": "escrowDeadline"` on the two fields, and `"title": "MkEscrow"` on the constructor.

- [ ] **Step 4: Validate against the CIP-57 meta-schema**

The meta-schema is in a **different git repository — do not commit there**:
`/Users/romainsoulat/Documents/GitHub/CIPs/CIP-0057/schemas/`

List that directory to find the right file, then validate the regenerated `Acme.golden.json`:

```bash
export PATH="/nix/var/nix/profiles/default/bin:$PATH"
nix run nixpkgs#check-jsonschema -- --schemafile <schema> plutus-tx-plugin/test/Blueprint/Acme.golden.json
```

Report the exact output. Add a **negative control** — a copy with a deliberately invalid field, validated to confirm it is rejected, then deleted — so the pass is not vacuous. If no validator is reachable, say so plainly rather than claiming a pass, and list which constraints you checked by hand instead.

- [ ] **Step 5: The acceptance check — does the Lean side now have what it needs?**

This is the point of the whole change, so verify it rather than assuming.

The consumer is `#import_blueprints` in the PlutusCoreBlaster package, vendored at
`/Users/romainsoulat/contracts-library/formal/.lake/packages/PlutusCore/PlutusCore/UPLC/BlueprintEncoding/Basic.lean`
(a **different repository — read only, commit nothing there**). Its
`emitStructType` path bails out when a constructor's fields have no names —
around line 586, and `emitSopType` names every variant after the type when
constructor titles are absent.

Read that code, then take the regenerated `Acme.golden.json` and answer
concretely: for `DatumPayload` (a record) and `Datum` (two constructors), does
the JSON now carry what those two functions read? Name the JSON keys they look
at and confirm each is present.

If a Lean toolchain is reachable you may go further and actually run
`#import_blueprints` over the regenerated blueprint — but **do not claim a pass
you did not observe**. Saying "the keys `emitStructType` reads are now present,
verified by reading both sides" is a useful result; claiming the Lean project
builds when you never ran Lean is not.

Report what you found either way. If the answer is no, that is the most
important finding of this task and the design needs revisiting.

- [ ] **Step 6: Commit**

```bash
nix develop --accept-flake-config --command bash -c 'git add plutus-tx plutus-tx-plugin doc && git commit -m "test(plutus-tx): regenerate blueprints with constructor and field titles

Acme.golden.json: Datums two variants are now distinguishable by title and
DatumPayloads fields carry their record names. Validated against the CIP-57
meta-schema."'
```

---

### Task 5: Changelog and documentation

**Files:**
- Create: `plutus-tx/changelog.d/20260904_000000_blueprint_field_names.md`
- Modify: `doc/docusaurus/docs/working-with-scripts/producing-a-blueprint.md`
- Modify: `docs/superpowers/specs/2026-09-03-blueprint-field-names-design.md`

- [ ] **Step 1: Write the changelog fragment**

Read the format first:
```bash
cat plutus-tx/changelog.d/20260816_000000_plutus_v4.md
```

Then create `plutus-tx/changelog.d/20260904_000000_blueprint_field_names.md` following it, with an `### Added` section covering `FieldSchema` and automatic field titles, and a `### Changed` section that says plainly:

- `ConstructorSchema`'s `fieldSchemas` field changed type from `[Schema referencedTypes]` to `[FieldSchema referencedTypes]`. **This is a breaking change to public API** — any code constructing a `ConstructorSchema` by hand must wrap each field in `MkFieldSchema Nothing`.
- A constructor's `title` now defaults to the constructor's own name rather than the type's. Blueprints regenerate with different (and CIP-57-conformant) titles. An explicit `SchemaTitle` annotation is unaffected.

- [ ] **Step 2: Update the user documentation**

`doc/docusaurus/docs/working-with-scripts/producing-a-blueprint.md` documents `SchemaTitle`/`SchemaDescription` around line 178. Add a short subsection saying that a record type's field names appear as each field's `title` automatically, with no annotation needed, and that a constructor's `title` defaults to the constructor name. Match the page's existing voice and use its `LiteralInclude` style if you reference example code.

- [ ] **Step 3: Record two things in the spec's open items**

In `docs/superpowers/specs/2026-09-03-blueprint-field-names-design.md`, §6 "Open questions", replace the two speculative questions with what you actually found, and add:

- **`plutus-tx/test/Blueprint/Definition/Spec.hs` is weaker than it reads.** Its `universe` call is at type `[SomeSchema] -> [[SomeSchema]]`, using lens's `Plated [a]` instance, so it walks the list spine and never descends into a `Schema`. It therefore only sees definition refs that are a definition's top-level schema. Not caused by this change and not fixed by it; worth fixing separately.
- Whatever you determined about `PlutusTx.AsData`-generated types (spec §4.2 left it open): do they produce constructor schemas, and if so are their field names recoverable? Answer it from the code and record the answer either way.

- [ ] **Step 4: Full verification**

Run all three suites and report each count:
```bash
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx:plutus-tx-test'
nix develop --accept-flake-config --command bash -c 'cabal test plutus-tx-plugin:plutus-tx-plugin-tests --test-options="-p Blueprint"'
nix develop --accept-flake-config --command bash -c 'cabal build plutus-ledger-api plutus-tx-plugin example-cip57 example-ual-blueprint'
```

- [ ] **Step 5: Commit**

```bash
nix develop --accept-flake-config --command bash -c 'git add plutus-tx/changelog.d doc docs && git commit -m "docs: field and constructor titles in blueprints

Changelog fragment records the breaking ConstructorSchema change and the
constructor-title default. The user guide says field names come from the
Haskell record automatically."'
```

---

## Notes on things that will bite

**`FieldSchema` must derive `Data`.** `Schema`'s `Plated` instance (`Schema.hs:63`) is `deriving anyclass`, and that class's default method is `Data`-based. Omit `Data` and the instance stops compiling — with an error pointing at line 63, not at your new type.

**`plutus-tx` compiles with `Strict`.** All data fields are strict, so a record with `error "…"` in one field is bottom as a whole. Do not construct partial `FieldSchema` values.

**`title` is an ambiguous name in `TH.hs`.** `deriveParameterBlueprint` and `deriveArgumentBlueprint` both bind a local `title`, and `SchemaInfo` has a `title` field selector. Task 3 touches code near both; if record-update syntax will not resolve, build the `SchemaInfo` explicitly rather than fighting the shadowing.

**Two `Text` aliases in one test module is legal but confusing.** If you end up importing both `Data.Text` and `Data.Text.Encoding` qualified, give them distinct aliases.

**`cabal run` from the repo root writes a stray golden tree** at `<repo-root>/test/`, because golden paths resolve relative to cwd. Use `cabal test`, or `cabal list-bin` plus a `cd` into a scratch directory.

**Do not accept a golden you have not read.** Task 4 exists because the constructor-title change alters output that a reviewer will scrutinise; `--accept` without reading the diff would cement whatever the code happens to do.
