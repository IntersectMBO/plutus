# UAL extended blueprints — design

**Date:** 2026-08-24
**Status:** approved design, not yet implemented
**Slice:** 1 of 3 (see [Scope](#8-scope))

## 1. Goal

Let a Plinth author annotate a contract's source with reusable predicates and
behavioural properties, and have the toolchain emit two machine-readable
documents describing them:

- `plutus.json` — a [CIP-0057](https://cips.cardano.org/cip/CIP-0057) blueprint,
  extended with the facts a verifier needs to *run* the compiled program:
  the ordered applied-argument list with encodings, and an execution budget.
- `assurance.json` — a document conforming to the *Plutus Blueprint Assurance
  Documents* CIP (draft, `CIP-XXXX` on branch `cip/extended-blueprints-verification`
  of `cardano-foundation/CIPs`), carrying the predicates and the properties.

The annotation language is UAL (Universal Annotation Language), specified in
[the UAL design doc](https://docs.google.com/document/d/1DgVjDwjCSLScUfEexVab27SmeWe9nGSiDCJ-TC_7ePM/edit).
UAL is deliberately surface-language agnostic; this slice delivers the Plinth
front end and the two output documents. A later slice consumes those documents
to generate a Lean 4 proof project.

## 2. Background: what already exists

Facts established by reading the code, all load-bearing for this design.

**On the Lean side** (`input-output-hk/PlutusCoreBlaster`, branch
`feat/blueprint-parsing`), `#import_blueprints <Name> "path/plutus.json"` already
reads a CIP-57 blueprint and generates both the `PlutusScript` instances and the
datum/redeemer Lean types with their `IsData` encodings, driven by the
blueprint's `definitions`. `contracts-library/formal/Formal/Vesting/Linear/` is
a hand-written instance of the target output:

| File | Content |
|---|---|
| `Script.lean` | `#import_blueprints LinearVesting "../onchain/plutus.json"`; `spendValidator := LinearVesting.…spend.script` |
| `Spec.lean` | pure-Lean predicates over the generated datum/redeemer types |
| `Soundness.lean` / `Completeness.lean` / `Robustness.lean` | one concern per file, theorems stated via `Formal.Common.validatorAccepts`, closed by `blaster` |

Note what is *not* there: `#prep_uplc`. Theorems are stated against
`validatorAccepts ctx validator = isSuccessful (cekExecuteProgram validator [toTerm ctx] 2500)`.
UAL doc §4 still describes the older `#prep_uplc` shape; see
[§9 UAL doc corrections](#9-ual-doc-corrections).

**On the Plutus side:**

- `plutus.json` is assembled by hand-written Haskell in a user-provided
  `gen-blueprint` executable — see
  `doc/docusaurus/static/code/Example/Cip57/Blueprint/Main.hs`. It is *not* GHC
  plugin output.
- The blueprint's `definitions` come from `HasBlueprintDefinition`, resolved at
  runtime in that executable. All the V1/V2/V3 ledger types, `ScriptContext`
  included, have instances (`plutus-ledger-api/src/PlutusLedgerApi/V3/Contexts.hs`
  alone has 21).
- The blueprint machinery already reads GHC `ANN` pragmas through Template
  Haskell's `reifyAnnotations` (`plutus-tx/src/PlutusTx/Blueprint/TH.hs:183`),
  for `SchemaTitle` / `SchemaDescription` / `SchemaComment`.
- The plugin has a path-valued option precedent (`certify`) that writes a
  project tree, and a `dump-uplc` option that writes flat bytes
  (`plutus-tx-plugin/src/PlutusTx/Plugin/Common.hs`).

**Consequence for the original request.** A single GHC compilation flag cannot
produce the artifacts. A Core plugin has no access to `HasBlueprintDefinition`
resolution, so a plugin-emitted blueprint would carry no `definitions`, and
every datum/redeemer type on the Lean side would degrade to raw `Data` (the
blueprint parser's `degradesToData` path). Aiken gets one-step generation because
`aiken build` emits `plutus.json` natively; Plinth needs
build → `gen-blueprint` → generate. This design accepts that and states it
explicitly rather than working around it.

## 3. Architecture

```
MyContract.hs                    {-@ ONCHAIN / PREDICATE / PROPERTY / UPLC_DATA -@}
    │
    ├── plinthc plugin ────────► CompiledCode                     (unchanged)
    │
    └── $(ualModule) ──────────► ModuleUal      [TH: reads own source, resolves names]
                                     │
        gen-blueprint exe ───────────┴──► plutus.json     (interface: arguments, budget, id)
                                          assurance.json  (claims: fragments, properties)
                                              │
                                    ual-gen (slice 2) ──► Lean project (script / spec / properties)
```

There is **no new GHC plugin flag** in this slice. In Plinth the thing that
produces the blueprint is the user's `gen-blueprint` executable, so UAL rides
the same path, as additional fields on `ContractBlueprint` and a second output
document. A flag reappears in slice 2, on `ual-gen`. Optionally, a plugin option
may later *validate* UAL blocks during `cabal build` without emitting anything;
that is not part of this slice.

## 4. Annotation surface and extraction

### 4.1 Syntax

UAL blocks are `{-@ … -@}` comments, as specified in the UAL doc. Comments,
rather than Template Haskell quasi-quotes or `ANN` pragmas, because UAL is
*universal*: the same block must be writable in Aiken and Scalus sources, and a
Haskell-specific surface would defeat that.

Four block kinds, per UAL doc §2. Two carry headers this design parses; two are
pass-through:

```haskell
{-@ ONCHAIN [version: PlutusV3] [exCPU: 1883313, exMem: 12342]
    mintingContract :: { CurrencySymbol : asData }
                    -> { ScriptContext  : asData }
                    -> ()
-@}

{-@ UPLC_DATA SellDatum -@}

{-@ PREDICATE
def sellerIsPaid (input : SpendingInput) : Prop := …
-@}

{-@ PROPERTY minting_success_imp_withdrawal
      "A successful mint implies the minting logic appears in the withdrawal map."
    : ∀ (cs : CurrencySymbol) (ctx : ScriptContext),
        validScriptContext ctx →
        isSuccessful (mintingContract cs ctx) →
        isMintingScriptInfo ctx
-@}
```

The `PROPERTY` natural-language string is **new**, added to UAL by this design.
It is required: the assurance CIP makes `statement.text` REQUIRED and rests its
central guarantee on it ("every claim remains legible to every reader —
including the users whose funds are at stake"). Without this field a producer has
nothing to put there.

### 4.2 Bodies are pass-through text

`PREDICATE` and `PROPERTY` bodies are Lean 4 source, checked by Lean's kernel
(UAL doc §3), and use PlutusCoreBlaster syntax such as `Recursor.any`. The
Haskell side therefore needs **no Lean parser**: it lexes the block, reads the
kind keyword and header, and passes the body through byte-identically. Only the
`ONCHAIN` refined signature needs real parsing. This is the difference between a
tractable slice and a compiler project.

### 4.3 Extraction: a TH splice, not a source plugin

The author adds one splice per annotated module:

```haskell
myContractUal :: ModuleUal
myContractUal = $(ualModule)
```

`ualModule` runs in `Q` and:

1. Takes the module's original source path from `TH.location` and reads it under
   `runIO`. `TH.location` reports the original `.hs` path, not the
   CPP-preprocessed file. Reading the raw source means a `{-@ … -@}` block inside
   a `#ifdef` is seen regardless of the branch taken; `Resolve` catches the
   common case, since a block guarded out will usually name something that does
   not resolve. Blocks under CPP are documented as unsupported.
2. Calls `addDependentFile` on it, so editing an annotation forces recompilation.
3. Lexes the `{-@ … -@}` blocks with source spans, parses the headers, and keeps
   bodies verbatim.
4. Resolves every `ONCHAIN` and `UPLC_DATA` name with `lookupValueName` /
   `lookupTypeName` and `reify`. **A typo'd name is a compile error**, and the
   reified type is checked against the refined signature's arity and argument
   types. This recovers the one guarantee comments would otherwise lose.
5. Returns a `ModuleUal` value.

Chosen over a GHC `parsedResultAction` phase with `Opt_KeepRawTokenStream`:
no comment-attachment fragility, no preprocessed-vs-original source confusion,
testable without a compiler, and the same shape as `makeIsDataSchemaIndexed`
already in the repo.

### 4.4 `ONCHAIN` on non-validator functions

UAL doc §2.2 annotates plain functions (`findScriptHash :: ByteString -> Integer
-> [TxInInfo] -> TxOut`), not only validators. Such a function compiles to a
standalone UPLC program with its own `compiledCode` and `hash`, which is
mechanically exactly what a CIP-57 validator entry describes — `validators` is
in substance "named compiled programs with argument schemas". So:

**An `ONCHAIN` function gets a blueprint `validators` entry.** Two consequences:

- The assurance CIP's "Validators only" rationale must widen (§8.3 below).
- In Plinth, UPLC exists only for expressions passed to `plinthc`/`plc`. An
  `ONCHAIN` function therefore needs a `CompiledCode`. The UAL TH helper
  generates the `compile` splice for it, so the author does not maintain that by
  hand.

## 5. Output: `plutus.json`

Three additional fields on validator objects. All are legal CIP-57 — validator
objects do not forbid additional fields, the same argument the assurance CIP
already makes for `id`:

```json
{
  "id": "minting-contract",
  "title": "mintingContract",
  "redeemer": { "…": "…" },
  "compiledCode": "…",
  "hash": "…",
  "arguments": [
    { "name": "pparamsCs", "encoding": "asData",
      "schema": { "$ref": "#/definitions/CurrencySymbol" } },
    { "name": "ctx", "encoding": "asData",
      "schema": { "$ref": "#/definitions/ScriptContext" } }
  ],
  "budget": { "exCPU": 1883313, "exMem": 12342 }
}
```

Design notes, each a correction to an earlier draft:

- **No `ual` wrapper key.** Argument encodings and execution budget are facts
  about the compiled program, not about UAL. Nesting them under a `ual` key
  privileges one verification language inside `plutus.json`, contradicting the
  assurance CIP's own rationale ("without either being privileged by the
  format"). Any verifier wants these fields.
- **No target-language type names.** Every argument type resolves to a `$ref`
  into `definitions`, because all ledger types have `HasBlueprintDefinition`
  instances. No Lean identifier leaks into the blueprint. The generator maps
  `$ref` targets to Lean types in slice 2, where that mapping belongs.
- **`arguments` is the one thing CIP-57 cannot express**: the ordered list of
  terms the program is applied to. CIP-57 splits `parameters` / `datum` /
  `redeemer` and leaves `ScriptContext` implicit; a wrapper must apply the
  program to concrete terms in order.
- **`version` is not stored per validator.** UAL's `[version: PlutusV3]`
  overlaps `preamble.plutusVersion`. Storing it twice invites disagreement;
  `Resolve` validates agreement instead. This is a deliberate limitation, not
  just a validation rule: CIP-57's preamble holds one Plutus version per
  contract, so **all validators in one contract must target the same version**.
  A contract mixing versions would need either a per-validator version field in
  the blueprint or one blueprint per version. Neither is in this slice.
- `encoding` is `asData` (default) or `asScott`. `asScott` is accepted and
  emitted by this slice but not yet consumable — see §8.
- **`budget` units are unresolved.** UAL specifies `exCPU`/`exMem`, which are
  Plutus cost-model units. The Lean side takes a *step* bound
  (`cekExecuteProgram validator args 2500`, `#prep_uplc … 5000`). These are
  different units and one does not determine the other without the cost model.
  This slice emits `exCPU`/`exMem` as UAL specifies them, since they are the
  meaningful on-chain quantity; converting to a step bound, or teaching the Lean
  CEK machine a budget in cost-model units, is slice 2's problem. Recorded in
  §11.

## 6. Output: `assurance.json`

Conforms to the assurance CIP, with **one new optional top-level field**,
`formalFragments`:

```json
{
  "$schema": "https://cips.cardano.org/cips/cipXXXX/schemas/assurance.json",
  "preamble": { "title": "…", "authors": ["…"], "created": "2026-08-24" },
  "blueprint": { "uri": "plutus.json", "hash": { "alg": "sha256", "digest": "…" } },
  "languages": { "ual": { "name": "Universal Annotation Language", "version": "0.4" } },
  "formalFragments": [
    { "id": "MyContract.Types", "language": "ual",
      "source": "def sellerIsPaid' … " },
    { "id": "MyContract", "language": "ual",
      "imports": ["MyContract.Types"],
      "source": "def sellerIsPaid … " }
  ],
  "properties": [
    { "id": "minting_success_imp_withdrawal",
      "title": "…",
      "scope": { "validators": ["minting-contract"] },
      "statement": {
        "text": "A successful mint implies the minting logic appears in the withdrawal map.",
        "formal": { "language": "ual", "uses": ["MyContract"], "source": "∀ …" }
      } }
  ]
}
```

**Why named fragments rather than one opaque preamble.** UAL has multiple
`PREDICATE` sections that reference earlier ones, and UAL doc §4 requires that
inter-module dependencies be preserved at the Lean level. A single concatenated
blob discards that. Here:

- a fragment `id` is the **surface module name**;
- its `source` is the concatenation of that module's `PREDICATE` block bodies in
  source order, separated by a blank line — source order matters, because UAL
  doc §2.1 lets a section reference definitions from earlier sections;
- `imports` mirror that module's imports, restricted to modules that produced a
  fragment;
- a property's `formal.uses` names the fragments its statement needs. A property
  in module M defaults to `uses: ["M"]`, or to `[]` when M produced no fragment;
  `imports` supplies the transitive closure, so `uses` need not spell it out.

**How `imports` is obtained.** Template Haskell cannot enumerate the current
module's imports, and `reify` on an imported name says nothing about whether its
module carries `PREDICATE` blocks — so the edges are not derivable from `Q`
alone. Instead the lexer collects `import` declarations in the same pass over the
raw source it already makes, and `ModuleUal` records its own module name
alongside that import list. The assembly step (§7.1) then intersects each
module's import list with the set of modules that actually produced fragments.
The restriction is therefore computed where the whole set is known, not
per-module.

This gives slice 2 real dependency information: one Lean file per surface module
in the predicates folder, and each property file importing only what it uses —
which is what makes Lean's per-file caching worth having (UAL doc §4).

**Evidence records are absent by construction.** This slice runs at build time,
before any proof. The CIP already names that state exactly: "a property with no
evidence records is a stated, unverified claim — a machine-readable
specification target". Blaster populates evidence in a later slice.

## 7. Component layout

New modules in `plutus-tx` (so they can reuse `PlutusTx.Blueprint` types
directly):

| Module | Responsibility |
|---|---|
| `PlutusTx.Ual.Syntax` | AST: `Onchain`, `Predicate`, `Property`, `UplcData`; `ModuleUal` |
| `PlutusTx.Ual.Lexer` | scan `{-@ … -@}` blocks → kind keyword, raw body, source span; collect `import` declarations in the same pass (§6) |
| `PlutusTx.Ual.Parser` | `ONCHAIN` refined signature and option lists; `PROPERTY` name + text; bodies verbatim |
| `PlutusTx.Ual.TH` | `ualModule :: Q Exp`; `addDependentFile`; `reify`-based name resolution; `compile`-splice generation for `ONCHAIN` functions |
| `PlutusTx.Ual.Resolve` | validation (see §8.2) |
| `PlutusTx.Blueprint.Validator` | + `validatorId`, `validatorArguments`, `validatorBudget` and their JSON |
| `PlutusTx.Assurance.*` | document types, `formalFragments`, `writeAssurance` |

**Source-breaking change.** New fields on `ValidatorBlueprint` break existing
record-construction sites. Mitigate with a `mkValidatorBlueprint` defaulting
helper and a scriv changelog fragment; `doc/docusaurus/static/code/Example/Cip57/`
must be updated in the same change.

### 7.1 The `ModuleUal` → blueprint seam

An `ONCHAIN` block names a Haskell binding (`mintingContract`); a
`ValidatorBlueprint` carries a prose `validatorTitle` ("My Validator"). Nothing
links them today, so the join key must be specified rather than left to the
implementation.

**`validatorId` is the join key, and the author never types it.** A TH splice
derives it from the reified name, so the two sides cannot drift:

```haskell
data ModuleUal = ModuleUal
  { ualModuleName    :: Text
  , ualModuleImports :: [Text]          -- §6
  , ualOnchain       :: [OnchainDecl]   -- each with its resolved binding name
  , ualPredicates    :: [Text]          -- bodies, source order
  , ualProperties    :: [PropertyDecl]
  , ualUplcData      :: [Text]
  }

ualModule :: Q Exp                      -- ~ ModuleUal, one splice per module
ualIdFor  :: Name -> Q Exp              -- ~ Text, the stable validator id
```

```haskell
myValidator =
  mkValidatorBlueprint
    { validatorId = Just $(ualIdFor 'mintingContract)
    , validatorTitle = "My Validator"
    , … }
```

**Validation splits by phase**, because a TH splice cannot see a runtime
blueprint value:

- *Compile time* (`Ual.TH`): checks 1, 2, 6 of §8.2 — name resolution, arity and
  argument-type agreement, `HasBlueprintDefinition` presence.
- *Assembly time* (`Ual.Resolve`, pure): checks 3, 4, 5, 7 — version agreement,
  fragment DAG and `uses` resolution, property-id uniqueness, and the
  `ONCHAIN`↔blueprint correspondence.

Two total functions carry it, and the author's `main` composes them in the order
the CIP's hash constraint demands:

```haskell
attachUal      :: [ModuleUal] -> ContractBlueprint
               -> Either [UalError] ContractBlueprint   -- fills arguments/budget/id
buildAssurance :: AssurancePreamble -> BlueprintRef -> [ModuleUal]
               -> Either [UalError] AssuranceDocument

main = do
  bp  <- orDie $ attachUal uals myContractBlueprint
  writeBlueprint "plutus.json" bp
  ref <- blueprintRef "plutus.json"        -- hash computed only once the file is final
  doc <- orDie $ buildAssurance myAssurancePreamble ref uals
  writeAssurance "assurance.json" doc
  where uals = [myContractUal, myTypesUal]
```

## 8. Scope

### 8.1 In scope

UAL lexer, parser, AST; TH extraction and name resolution; the `Resolve`
validation pass; the three blueprint fields with JSON encoding; the assurance
document types and writer; the CIP revisions of §8.3; the UAL doc corrections of
§9.

### 8.2 Validation performed by `Resolve`

1. Every `ONCHAIN` / `UPLC_DATA` name resolves in the module.
2. The refined signature's arity and argument types agree with the reified
   Haskell type.
3. `[version: …]` agrees with `preamble.plutusVersion`.
4. Every `formal.uses` entry names an existing fragment; fragment `imports` form
   a DAG.
5. Property `id`s are unique within the document (a CIP consumer obligation, so
   the producer must not emit violations).
6. Every `UPLC_DATA` type has a `HasBlueprintDefinition` instance, so it will
   appear in `definitions`.
7. Every `ONCHAIN` name has a blueprint entry whose `validatorId` matches, every
   `validatorId` is unique within the contract, and no blueprint entry carries
   `arguments`/`budget` without a corresponding `ONCHAIN` block.

Checks 1, 2 and 6 run at compile time in the splice; 3, 4, 5 and 7 run at
assembly time, per §7.1.

### 8.3 CIP revisions required

The CIP is at `CIP-XXXX/README.md` on branch
`cip/extended-blueprints-verification` of the local `CIPs` checkout.

1. **Rationale reason #2 is wrong for this case.** It argues against embedding
   assurance data in `plutus.json` because "hand-maintained assurance data
   embedded in a generated file would be overwritten on each compilation". When
   the content comes from source annotations and the toolchain generates it,
   nothing is hand-maintained and regeneration is harmless. Rewrite the reason to
   distinguish hand-maintained from generated content, and make
   source-annotated generation a first-class producer mode. Detachment survives
   on reasons #1 (third-party publishing) and #3 (no `$vocabulary` machinery),
   both untouched.
2. **Add `formalFragments`** (§6), with the consumer obligation that fragments
   are opaque per-language text and unknown language keys are ignored.
3. **Widen "Validators only"** to cover `ONCHAIN` functions emitted as validator
   entries (§4.4).
4. **Add a "Producers" subsection**: deterministic output, `preamble.authors` and
   `created` from project metadata, and the build ordering constraint that
   `blueprint.hash` can only be computed once `plutus.json` is final.
5. **Blueprint companion fields are documented in the UAL spec, not the CIP.**
   The CIP stays language-agnostic; it gains only a note that a
   `formal.language` implementation may require additional, CIP-57-legal
   blueprint fields.
6. Promote validator `id` from RECOMMENDED to "emitted by the Plinth producer".

### 8.4 Out of scope (later slices)

- **Slice 2 — the generator**: extended `plutus.json` + `assurance.json` → the
  Lean project tree (script/wiring, predicates, one file per property with a
  `blaster` call), plus a templated `lakefile.toml`. Its acceptance test is a
  diff against `contracts-library/formal/Formal/Vesting/Linear/`.
- **Slice 3 — evidence**: Blaster populates `evidence` records with outcomes,
  script hashes and proof artifacts.
- `asScott` consumption. `CardanoLedgerApi` has `IsData` (`IsData/Class.lean`)
  but **no `IsScott`**, which UAL doc §2.3 promises and §2.2's `asScott` depends
  on. Upstream Lean dependency.
- `PlutusV4`. UAL doc §2.2 lists it; the Lean parser's
  `plutusVersionToLangExpr` errors past V3.
- Aiken and Scalus front ends. The output documents are the interoperability
  point, so those front ends need no change here.

## 9. UAL doc corrections

Not CIP issues; corrections to the UAL design doc, to be made alongside this
work.

1. **§4's `#prep_uplc` is superseded.** The current Lean shape imports the
   blueprint and states theorems against `validatorAccepts` (§2). The
   generalisation UAL's refined signature implies is a **per-function wrapper**:

   ```lean
   def mintingContract (cs : CurrencySymbol) (ctx : ScriptContext) : HaltState :=
     cekExecuteProgram MyBp.mintingContract.script [toTerm cs, toTerm ctx] 1883313
   ```

   which is what makes UAL's own `isSuccessful (mintingContract cs ctx)`
   elaborate, with `validatorAccepts` as the single-argument special case. This
   is precisely what the `arguments` and `budget` blueprint fields exist to
   drive.
2. **§4's import direction is inverted.** It says "if a module M1 imports a
   module M2 … the elaborated Lean4 module M2Predicates will import Lean4 module
   M1Predicates". M1 depends on M2, so `M1Predicates` imports `M2Predicates`.
   §6's `formalFragments.imports` implements the correct direction.
3. **§2.4 needs the natural-language field** added in §4.1.
4. §2.2's `PlutusV4` and §2.3's `IsScott` are ahead of the Lean implementation
   (§8.4).
5. The open comment thread on §2.1 — "why would users write that in Lean instead
   of their original language?" — is recorded as decided in favour of UAL for
   now. Nothing in this design forecloses a Haskell-to-Lean predicate compiler
   later: it would be an additional front end producing the same
   `formalFragments`.

## 10. Testing

- **Golden tests**: annotated fixture modules → expected `plutus.json` and
  `assurance.json`, following the existing `plutus-tx-plugin/test/Blueprint/Tests.hs`.
- **Schema conformance**: validate every emitted `assurance.json` against
  `CIP-XXXX/schemas/assurance.json`.
- **Byte-identity**: property test that `PREDICATE` / `PROPERTY` bodies survive
  extraction unchanged, including Unicode and nested `{- -}`.
- **Negative tests**: one per `Resolve` check in §8.2.
- **Acceptance**: hand-write the document pair for linear vesting and confirm it
  carries everything `Formal/Vesting/Linear/{Script,Spec,Soundness}.lean` needs —
  `arguments`/`encoding`/`budget` for `spendValidator`, the `Spec.lean`
  predicates as fragments, the `Soundness.lean` theorems as properties. A paper
  exercise in this slice; executable in slice 2.

## 11. Open items

- Whether `plutus-tx` is the right home, or whether UAL should be its own package
  to avoid growing `plutus-tx`'s surface. Decided in favour of `plutus-tx` for
  now, to share `PlutusTx.Blueprint` types without a new dependency edge.
- The exact `mkValidatorBlueprint` signature and how much of the source-breaking
  change to absorb behind it.
- Whether `ual-gen` (slice 2) lives in this repo or alongside
  `#import_blueprints`. Not decided here; the document pair is the interface
  either way.
- Reconciling `exCPU`/`exMem` with the Lean CEK machine's step bound (§5). Needs
  either a cost-model-driven conversion or a budget-aware `cekExecuteProgram`
  upstream. Blocks nothing in this slice.
