# Linear-vesting acceptance check for the UAL document pair

Spec §10 calls this "the acceptance test that matters": does the pair of
documents the UAL pipeline emits — an extended CIP-57 `plutus.json` and an
`assurance.json` — carry everything a generator would need to produce the Lean
project a human already wrote by hand?

The reference is `/Users/romainsoulat/contracts-library/formal/Formal/Vesting/Linear/`
(`Script.lean`, `Spec.lean`, `Soundness.lean`, `Completeness.lean`,
`Robustness.lean`), against
`/Users/romainsoulat/contracts-library/formal/Formal/Common.lean` and the Aiken
blueprint at `/Users/romainsoulat/contracts-library/onchain/plutus.json`. That is
a separate repository; nothing here modifies it.

This is a paper exercise. Slice 2 generates the Lean; slice 3 adds evidence.
The point of doing it now is that the format is still cheap to change.

Two facts shape everything below.

- **The reference project builds against an _Aiken_ blueprint**, not one this
  pipeline produced. `Script.lean:4` says so: "`#import_blueprints` reads the
  CIP-57 blueprint `../onchain/plutus.json` (produced by `aiken build`)". The
  hand-written pair in §2 is therefore a hypothetical Plinth port of the same
  contract, and the interesting question is where the two blueprints differ.
- **`#import_blueprints` today reads none of the three fields UAL adds.**
  Walking `BlueprintEncoding/Basic.lean:769-806`, it consumes `preamble`,
  per-validator `title`, `compiledCode`, `hash`, `datum`, `redeemer`,
  `parameters`, and the whole `definitions` map. It never looks at `id`,
  `arguments` or `budget`. Slice 2 is a change on the Lean side as well as a
  generator.

---

## 1. What the five Lean modules consume

Everything each module needs that is not Lean source the module already
contains.

| Lean identifier | Defined where | Would have to come from |
| --- | --- | --- |
| `LinearVesting.linear_vesting_linear_vesting_spend.script` | `#import_blueprints`, from `compiledCode` | blueprint `validators[].compiledCode`, named by `sanitizeName` of `validators[].title` |
| `LinearVesting.VestingDatum` + fields `beneficiary`/`locker`/`vesting`/`start_time`/`end_time`/`recovery_time` | `#import_blueprints`, from `definitions` | blueprint `definitions` — needs per-**field** `title` |
| `LinearVesting.VestingRedeemer.Claim` / `.Cancel` | ditto | blueprint `definitions` — needs per-**constructor** `title` |
| `LinearVesting.Credential.VerificationKey` / `.Script`, `LinearVesting.VestedAsset` | ditto | ditto |
| `IsData.toData` for each of the above | `#import_blueprints` emits the instances | derived from the same `definitions` |
| the applied-argument list `[toTerm ctx]` | `Common.lean:22` | blueprint `arguments` (arity + `encoding`) |
| the execution bound `2500` | `Common.lean:22`, a literal | **nothing** — blueprint `budget` is in different units (§3.2) |
| `validatorAccepts` / `validatorRejects` | `Formal/Common.lean:21-27`, a shared library module | not in the pair; a generator prelude, but see §3.3 |
| `vested`, `required`, `validSchedule` | `Spec.lean:33-71` | a `PREDICATE` block → `formalFragments[].source` |
| `dSched`, `dConcrete`, `dScript` | `Spec.lean:77-101` | ditto |
| `scriptHash`, `scriptAddress`, `validRangeData`, `withAsset`, `baseTxInfo`, `mkClaimCtx`, `mkClaimCtxW`, `mkClaimCtxHashInput`, `mkClaimCtxDouble` | `Soundness.lean:31-139` | ditto |
| `import Blaster`, `import PlutusCore.UPLC`, `import CardanoLedgerApi.V3`, `import CardanoLedgerApi.V1.Time`, `import Formal.Common` | the five modules' import lists | **nothing** — `formalFragments[].imports` cannot carry them (§3.4) |
| the tactic (`blaster`, `blaster (timeout: 10)`) closing each theorem | written per theorem | not in the pair; the generator must pick one (§5) |

Three observations on that list.

`Common.lean:22` applies the program to exactly one argument:

```lean
def validatorAccepts (ctx : ScriptContext) (validator : Program) : Prop :=
  isSuccessful (cekExecuteProgram validator [toTerm ctx] 2500)
```

So for a V3 spend validator the whole of `arguments` is one entry. Since
CIP-0069 the datum and redeemer live inside the `ScriptContext`, so the domain
types (`VestingDatum`, `VestingRedeemer`) do **not** appear in `arguments` at
all; they reach the pair through CIP-57's `datum` and `redeemer` schemas, which
is what puts them in `definitions` where `#import_blueprints` finds them.
`arguments` carries arity and encoding, and that is precisely what spec §9.1's
per-function wrapper needs. It is sufficient for its purpose.

`Spec.lean:42-53` is explicit that the datum/redeemer types are *not*
hand-written Lean but generated from the blueprint, "so the spec is now tied to
the actual compiled schema rather than a mirror that could drift". That design
decision is what makes §3.1 the headline gap: the types are load-bearing and
they arrive entirely through `definitions`.

`Soundness.lean:28-139` — 110 lines of ledger-context scaffolding — is
*definitions*, not theorems, despite living in a module named after a proof
direction. It rides in the pair perfectly well as a `PREDICATE` block. What the
pair cannot reproduce is the reference's *placement* of it (§3.6).

---

## 2. The hand-written document pair

A hypothetical Plinth port with one annotated surface module `Vesting.Linear`
and its types module `Vesting.Linear.Types`. `compiledCode` and `hash` are
elided for length; the budget figure is discussed below.

### 2.1 `plutus.json` — the `validators` entry

```json
{
  "id": "spendValidator",
  "title": "spendValidator",
  "description": "Linear vesting: the beneficiary claims vested assets; the locker recovers the remainder after the recovery time.",
  "datum": {
    "title": "VestingDatum",
    "purpose": "spend",
    "schema": { "$ref": "#/definitions/VestingDatum" }
  },
  "redeemer": {
    "title": "VestingRedeemer",
    "purpose": "spend",
    "schema": { "$ref": "#/definitions/VestingRedeemer" }
  },
  "compiledCode": "<flat script, hex — elided>",
  "hash": "<blake2b-224 of 0x03 <> compiledCode — elided>",
  "arguments": [{ "encoding": "asData", "schema": { "$ref": "#/definitions/BuiltinData" } }],
  "budget": { "exCPU": 0, "exMem": 0 }
}
```

The budget is zero deliberately. No measurement for this script exists in
either repository — the reference project's only execution number is the literal
`2500` in `Common.lean`, which is in different units — and inventing one would
defeat the exercise. Zeros are also a clean demonstration that the field is
load-bearing: `cekExecuteProgramWithBudget` (`CekMachine.lean:353`) checks
`if budget.canAfford costs.startupCost` and returns `BudgetExhausted` before the
first step, so a zero budget makes every property false rather than silently
weak.

`id` and `title` coincide here only because the author wrote them that way.
`ualIdFor` is `nameBase` of the Haskell name (`Ual/TH.hs:84-85`), `title` is set
by hand, and `attachUal` never touches `title` (`Ual/Resolve.hs`, the comment on
`fill`). The generator has to join `scope.validators` (an `id`) through the
blueprint to `title` and then through `sanitizeName` to get the Lean name — for
the real Aiken blueprint that chain is
`linear_vesting.linear_vesting.spend` → `linear_vesting_linear_vesting_spend`,
which is exactly what `Script.lean:22` writes.

### 2.2 `plutus.json` — `definitions`, as this pipeline emits them

This is the whole of §3.1 in one comparison. What the reference needs, from
Aiken:

```json
"vesting/types/VestingDatum": {
  "title": "VestingDatum",
  "anyOf": [{
    "title": "VestingDatum", "dataType": "constructor", "index": 0,
    "fields": [
      { "title": "beneficiary",    "$ref": "#/definitions/cardano~1address~1Credential" },
      { "title": "locker",         "$ref": "#/definitions/cardano~1address~1Credential" },
      { "title": "vesting",        "$ref": "#/definitions/List<vesting~1types~1VestedAsset>" },
      { "title": "start_time",     "$ref": "#/definitions/Int" },
      { "title": "end_time",       "$ref": "#/definitions/Int" },
      { "title": "recovery_time",  "$ref": "#/definitions/Int" }
    ]
  }]
}
```

What `deriveDefinitions` can emit for the same record, in the shape
`plutus-tx-plugin/test/Blueprint/Acme.golden.json` shows for `DatumPayload`:

```json
"VestingDatum": {
  "$comment": "MkVestingDatum",
  "dataType": "constructor",
  "index": 0,
  "fields": [
    { "$ref": "#/definitions/Credential" },
    { "$ref": "#/definitions/Credential" },
    { "$ref": "#/definitions/List_VestedAsset" },
    { "$ref": "#/definitions/Integer" },
    { "$ref": "#/definitions/Integer" },
    { "$ref": "#/definitions/Integer" }
  ]
}
```

### 2.3 `assurance.json` — `formalFragments`

Two fragments, one per surface module, ids being the module names, with
`Vesting.Linear`'s single `imports` entry being the one import that is also a
fragment. The sources below name the datum's fields and the redeemer's
constructors as Aiken emits them, because that is what the reference proofs are
written against; §3.1 is why this pipeline's `definitions` cannot supply those
names.

```json
"formalFragments": [
  {
    "id": "Vesting.Linear.Types",
    "language": "ual",
    "source": "def vested (T start finish now : Int) : Int :=\n  if now ≤ start then 0\n  else if finish ≤ now then T\n  else T * (now - start) / (finish - start)\n\ndef required (T start finish now : Int) : Int :=\n  T - vested T start finish now\n\ndef validSchedule (d : VestingDatum) : Prop :=\n  d.start_time < d.end_time ∧ d.end_time < d.recovery_time\n\ndef datumData (d : VestingDatum) : Data := IsData.toData d\ndef claimRedeemer  : Data := IsData.toData VestingRedeemer.Claim\ndef cancelRedeemer : Data := IsData.toData VestingRedeemer.Cancel"
  },
  {
    "id": "Vesting.Linear",
    "language": "ual",
    "imports": ["Vesting.Linear.Types"],
    "source": "def scriptHash : ByteString := \"fake_script_hash_28bytes!!!!\"\ndef scriptAddress : Address := ⟨.ScriptCredential scriptHash, none⟩\n\ndef validRangeData (now : Int) : Data :=\n  IsData.toData (CardanoLedgerApi.V1.Time.after now)\n\ndef withAsset (lovelace : Int) (policy name : ByteString) (qty : Int) : Value :=\n  [(Data.B \"\", Data.Map [(Data.B \"\", Data.I lovelace)]),\n   (Data.B policy, Data.Map [(Data.B name, Data.I qty)])]\n\ndef baseTxInfo (now : Int) (signatories : List ByteString) : TxInfo := …\ndef mkClaimCtxW (datum : VestingDatum) … : ScriptContext := …\ndef mkClaimCtx (datum : VestingDatum) … : ScriptContext := …\ndef mkClaimCtxHashInput … : ScriptContext := …\ndef mkClaimCtxDouble … : ScriptContext := …\n\ndef dSched (bene locker policy name : ByteString) (total start finish recovery : Int) : VestingDatum := …\ndef dConcrete : VestingDatum := dSched \"beneficiary_key_hash\" \"locker_key_hash\" \"policyA\" \"assetA\" 100 1000 2000 3000\ndef dScript (bhash : ByteString) : VestingDatum := …"
  }
]
```

The five bodies marked `…` are `Soundness.lean:44-139` and `Spec.lean:77-101`
verbatim; they are elided for length, not because anything stops them being
carried. The `validRangeData` body is shown in full on purpose: it is the only
definition here that needs `CardanoLedgerApi.V1.Time` (`Soundness.lean:11`), an
import the pair drops (§3.4).

### 2.4 `assurance.json` — `properties` from `Soundness.lean`

Three theorems, `Soundness.lean:149`, `:184`, `:204`. `text` is the
parenthetical gloss from `README.md:64-70`'s Soundness table; the `formal.source`
turns each theorem's binders and hypotheses into a single closed proposition,
because a property has no binder field.

```json
[
  {
    "id": "claim_sound_partial",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "Acceptance forces datum reproduction and at least the required remainder (I2 + I3).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (d : VestingDatum) (a : VestedAsset) (inLovelace outLovelace inQty outQty now : Int) (outAddr : Address) (outDatum : Data),\n  d.vesting = [a] ∧ validSchedule d ∧ now < d.end_time ∧\n  validatorAccepts (mkClaimCtx d (withAsset inLovelace a.policy a.name inQty) outAddr (withAsset outLovelace a.policy a.name outQty) outDatum now (match d.beneficiary with | .VerificationKey h => [h] | .Script _ => []) claimRedeemer) spendValidator →\n    outDatum = datumData d ∧ outQty ≥ required a.total d.start_time d.end_time now"
      }
    }
  },
  {
    "id": "claim_sound_partial_concrete",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "For the standard instance, acceptance forces the continuation to reproduce the datum and to hold at least the required remainder of 50 at now = 1500.",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (outQty : Int) (outDatum : Data),\n  validatorAccepts (mkClaimCtx dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" outQty) outDatum 1500 [\"beneficiary_key_hash\"] claimRedeemer) spendValidator →\n    outDatum = datumData dConcrete ∧ outQty ≥ 50"
      }
    }
  },
  {
    "id": "cancel_sound",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "Acceptance forces now > recovery_time: the locker cannot recover before the recovery time (I5 / C7).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (now : Int),\n  validatorAccepts (mkClaimCtx dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" 100) (datumData dConcrete) now [\"locker_key_hash\"] cancelRedeemer) spendValidator →\n    3000 < now"
      }
    }
  }
]
```

All three carry `sorry` in the reference (`Soundness.lean:168`, `:196`, `:216`).
They are *stated*, not proved — which is exactly the case the CIP describes for
a property with no evidence record, so the pair represents them correctly.

### 2.5 `assurance.json` — `properties` from `Robustness.lean`

Five of the twelve theorems, chosen because each is a distinct shape. `text`
comes from `README.md:51-62`'s Robustness table.

```json
[
  {
    "id": "reject_wrong_signer",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "An unauthorized claim is rejected: a claim signed by a key that is not the beneficiary fails the authorization check (R1).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (w : ByteString), w ≠ \"beneficiary_key_hash\" →\n  validatorRejects (mkClaimCtx dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" 100) (datumData dConcrete) 1500 [w] claimRedeemer) spendValidator"
      }
    }
  },
  {
    "id": "reject_over_release_concrete",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "Over-release is rejected: a claim whose continuation keeps less than the required remainder fails the remainder check (R2).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (outQty : Int), outQty < required 100 1000 2000 1500 →\n  validatorRejects (mkClaimCtx dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" outQty) (datumData dConcrete) 1500 [\"beneficiary_key_hash\"] claimRedeemer) spendValidator"
      }
    }
  },
  {
    "id": "reject_datum_hash_input",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "A datum-hash input is rejected: the validator requires an inline datum on its own input (R4).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (datumHash : ByteString),\n  validatorRejects (mkClaimCtxHashInput dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) datumHash scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" 100) (datumData dConcrete) 1500 [\"beneficiary_key_hash\"] claimRedeemer) spendValidator"
      }
    }
  },
  {
    "id": "reject_premature_cancel",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "A cancel before the recovery time is rejected; the bound is strict (R6).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "∀ (now : Int), now ≤ 3000 →\n  validatorRejects (mkClaimCtx dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) scriptAddress (withAsset 2000000 \"policyA\" \"assetA\" 100) (datumData dConcrete) now [\"locker_key_hash\"] cancelRedeemer) spendValidator"
      }
    }
  },
  {
    "id": "no_double_satisfaction",
    "scope": { "validators": ["spendValidator"] },
    "statement": {
      "text": "One continuation cannot satisfy two inputs: the k-scaling rule forces k × required (§5.1, I2).",
      "formal": {
        "language": "ual",
        "uses": ["Vesting.Linear"],
        "source": "validatorRejects (mkClaimCtxDouble dConcrete (withAsset 2000000 \"policyA\" \"assetA\" 100) (withAsset 2000000 \"policyA\" \"assetA\" 50) (datumData dConcrete) 1500 [\"beneficiary_key_hash\"] claimRedeemer) spendValidator"
      }
    }
  }
]
```

The seven omitted (`reject_unauthorized_claim`,
`reject_unauthorized_claim_no_sig`, `reject_over_release`,
`reject_datum_tamper`, `reject_datum_tamper_concrete`,
`reject_script_no_withdrawal`, `reject_unauthorized_cancel`) instantiate the same
shapes and are omitted for length, not because the format struggles with them.

Note what the emission does **not** need: a polarity field. `formal.source` is
verbatim text, so `validatorRejects` is carried as written. Polarity turns out
not to be a format gap at all — the difficulty with the rejection theorems is in
the *meaning* of `validatorRejects`, which is §3.2.

---

## 3. Gaps

### 3.1 Plinth-derived `definitions` cannot produce the datum/redeemer Lean types — BLOCKING, blueprint

The reference project builds because `aiken build` emits per-field and
per-constructor `title`s. `Spec.lean:71`'s `d.start_time < d.end_time ∧
d.end_time < d.recovery_time` uses Aiken's snake_case field names, and
`Spec.lean:79-80`'s `.VerificationKey bene` / `Spec.lean:64-65`'s
`VestingRedeemer.Claim` use Aiken's constructor names. Both come out of
`definitions` (§2.2).

`#import_blueprints` requires them. `BlueprintEncoding/Basic.lean:586-589`'s
`emitStructType` filters to named fields and then bails:

```lean
  if namedFields.length != fields.length then
    logWarning s!"Blueprint: record '{typeName}' has positional (unnamed) fields; \
no Lean type emitted (the slot stays raw Data)."
    return
```

and `emitSopType` reads the constructor name from each variant's `title`:

```lean
  let ctors : List (String × Nat × List PlutusType) := variants.filterMap fun
    | .constr (some t) idx fields => some (sanitizeName t, idx, fields.map (·.2))
```

This pipeline cannot supply either.

- **Field names are not representable.** `PlutusTx.Blueprint.Schema:238-241`
  defines `ConstructorSchema` with `fieldSchemas :: [Schema referencedTypes]` —
  a bare list, no name slot — serialised at `Schema.hs:101` as
  `requiredField "fields" fieldSchemas`. There is nowhere to put a field name,
  so `emitStructType` always hits the guard above and emits nothing: no
  `VestingDatum`, and `Script.lean:19`'s `#print LinearVesting.VestingDatum`
  fails.
- **Constructor names go to the wrong key.** `Acme.golden.json`'s `Datum` shows
  the type name in every variant's `title` and the constructor name in
  `description`: `{"title": "Datum", "description": "DatumLeft"}`. So
  `emitSopType` would name both variants `Datum`, and
  `Credential.VerificationKey` / `.Script` and `VestingRedeemer.Claim` /
  `.Cancel` are unreachable.

**Fix**: add a per-field name to `ConstructorSchema` (Aiken puts it in `title`,
which is CIP-57-legal), and put the constructor name in each variant's `title`
where Aiken puts it, keeping the type name where it already is. Blueprint side,
in `plutus-tx`. Nothing in the assurance document is involved.

**Blocking.** Replacing the Aiken blueprint with this pipeline's output breaks a
project that currently builds — and would break it *quietly*, with
`logWarning`s and downstream elaboration errors rather than a blueprint-level
diagnostic.

### 3.2 `exCPU`/`exMem` versus the step bound — NOT blocking, but the fix is not a conversion

`Common.lean:22` passes `2500` to `cekExecuteProgram`, a CEK **step** count. UAL
declares cost-model units, and spec §9.1's own example substitutes an exCPU
figure straight into that slot:

```lean
   def mintingContract (cs : CurrencySymbol) (ctx : ScriptContext) : HaltState :=
     cekExecuteProgram MyBp.mintingContract.script [toTerm cs, toTerm ctx] 1883313
```

`1883313` is the `exCPU` from the golden budget. The units confusion is already
in the design document.

It matters most on the rejection side, because step exhaustion is
indistinguishable from a script error. `CekMachine.lean:242-247`:

```lean
def runSteps (semanticsVariant : BuiltinSemanticsVariant) (Sigma : State) (n : Nat) : State :=
  match n, Sigma with
  | _, State.Halt V => Sigma
  | _, State.Error => Sigma
  | 0, _ => State.Error -- change to error when num steps exhausted
  | Nat.succ n, _ => runSteps semanticsVariant (step semanticsVariant Sigma) n
```

and `Utils.lean:29-34` gives `isSuccessful = isHaltState`, which cannot tell the
two `State.Error`s apart. So `validatorRejects` as stated is "errors **or** runs
past 2500 steps".

To be clear about what this does and does not mean: the reference's rejection
theorems are sound *in fact*, because `Completeness.lean:62`'s
`claim_accept_concrete` proves `validatorAccepts` on the same validator at the
same bound over a near-identical context, so 2500 demonstrably suffices for this
script to reach `Halt`. But that argument lives entirely outside the document
pair, is per-context, and breaks silently if the bound is tightened or the script
grows. A rejection theorem should not depend on an accept-side theorem elsewhere
in the project for its meaning.

**The conversion problem dissolves rather than needing solving.** The Lean
library already has a budget-aware evaluator that consumes exactly what the
blueprint declares — `CekMachine.lean:342-358`:

```lean
def cekExecuteProgramWithBudget
    (p : Program) (plutusVer : PlutusVersion) (protocolVer : ProtocolVersion)
    (params : List Term) (budget : ExBudget) : EvaluationResult
```

with `EvaluationResult` (`CekMachine.lean:44-47`) splitting `Success` /
`BudgetExhausted` / `EvaluationError`. Acceptance is `Success _ _`; rejection is
`EvaluationError`, with `BudgetExhausted` a third, honest outcome instead of
being folded into rejection.

So the fix depends on one thing I could not check here — whether `blaster` can
symbolically execute the budget-aware machine, whose every step carries budget
arithmetic, and whose `runStepsWithBudget` termination proof is `sorry`
(`CekMachine.lean:326-327`). Two branches:

- **If tractable**: the fix is in `Formal/Common.lean`, not the format.
  `exCPU`/`exMem` are already the right currency. The blueprint needs only a
  cost-model selector — `ProtocolVersion` is pre-/post-Conway
  (`Default/Basic.lean:37-39`) and defaults to `postConway`, so this is small —
  plus budget provenance, since the Lean library hard-codes
  `defaultCekMachineCosts{A..E}` (`CekMachine.lean:335-341`) while the producer
  measures under whatever cost model it had (the constitution example's own
  haddock says `defaultCekParametersForTesting`). A budget nobody can attribute
  to a cost model is a number, not a bound.
- **If not tractable**: the format needs a producer-computed step bound
  alongside `exCPU`/`exMem`, because deriving one requires the cost model and
  only the producer has it. That lands in the blueprint's `budget` object.

**Not blocking** either way — a generator can emit the reference's own literal —
but it is the difference between a bound the proofs can rely on and a bound they
happen to survive.

### 3.3 Nothing in the pair binds the validator into a formal statement — assurance + UAL syntax

Every property in the reference mentions the compiled program:
`Soundness.lean:163` is `validatorAccepts ctx spendValidator`. The pair has the
material to *define* that name (§2.1's join from `id` through `title`), but
nothing that says which name the property source will use. UAL provides no
reserved identifier for "the script this property is scoped to" and no
acceptance predicate.

The consequence is visible in the pipeline's own worked example. Rather than
naming the validator, `Example/Ual/Blueprint/Main.hs` axiomatises it:

```haskell
-- The outcome of the constitution script on a well-formed ProposingScript
-- ScriptContext whose ProposalProcedure carries the given governance action.
axiom verdict : GovAction → Verdict
```

and then states all five properties about `verdict`. Nothing connects `verdict`
to `compiledCode`, so those five properties are provable without the script
existing — the opposite of what `Soundness.lean` does.

**Fix**: write the naming contract down. Either specify that a `formal.language`
implementation binds each `scope.validators` id as an in-scope name (plus an
`accepts`/`rejects` predicate over it), or have UAL emit the wrapper of spec
§9.1 per `ONCHAIN` block and name it. Assurance document and UAL syntax.

**Blocking**, because slice 2's acceptance test is a diff against the reference
(spec §8.4) and this decides every theorem statement in it. It is also the
cheapest thing on this list to fix now and the most expensive to fix after the
CIP is published.

### 3.4 Fragment `imports` drop non-fragments, and nothing names the dialect or its libraries — BLOCKING, assurance

`Assurance/Build.hs:92-93` restricts a fragment's imports to modules that are
themselves fragments:

```haskell
          , fragmentImports =
              [i | imp <- ualModuleImports m, let i = nameOf imp, Set.member i fragmentIds]
```

Everything else is dropped silently. The reference needs `import Blaster`,
`import PlutusCore.UPLC`, `import CardanoLedgerApi.V3` and `import Formal.Common`
in every proof module, and `import CardanoLedgerApi.V1.Time` in
`Soundness.lean:11` — the last needed only because `validRangeData`
(`Soundness.lean:36`) calls `CardanoLedgerApi.V1.Time.after`. A generator can
hardcode a prelude for the fixed four; the fifth is contract-specific and
unrecoverable from the pair.

The same gap has a second half. `fragmentLanguage` and `formalLanguage` are
always the literal `"ual"` (`Assurance/Build.hs:26`, `:91`, `:112`) while the
bodies are Lean 4 against `PlutusCore` and `Blaster`, and the `languages`
registry pins UAL 0.4 (`Build.hs:147-154`) — not the Lean toolchain, not the
library versions. Slice 2 is committed to emitting a `lakefile.toml`
(spec §8.4) and the pair says nothing about what goes in it.

**Fix**: a separate field for external imports, so the cycle check
(`Build.hs:141-145`) keeps operating on fragment ids only; and either a dialect
tag distinct from the language key or per-language dependency metadata in the
`languages` registry entry. Assurance document.

**Blocking** for a generator that must produce a buildable project.

### 3.5 Per-property scope is simultaneously too coarse and too narrow — assurance + UAL syntax

`Assurance/Build.hs:106` scopes every property to the one id passed in:

```haskell
          , propertyValidators = [defaultValidator]
```

from `buildAssurance`'s third argument (`Build.hs:59-60`), and `PropertyDecl`
(`Ual/Syntax.hs:91-99`) has name, text, body and line — no scope. The docstring
is candid about it.

Two directions, and linear vesting exposes both more than expected.

**Too coarse.** The reference blueprint is not single-validator: `aiken build`
emitted `linear_vesting.linear_vesting.spend` *and*
`linear_vesting.linear_vesting.else`, sharing one `compiledCode` and hash. The
proofs target only `spend`. A single global scope can name `spend`, so nothing
breaks here — but no property could ever be stated about `else`, and for a
genuinely multi-validator contract the output is not merely incomplete, it is
false: properties about validator B are published as claims about validator A.
That is worse than an omission.

**Too narrow.** `README.md:30-38` tables six theorems about the pure schedule
arithmetic — `vested_preStart`, `vested_full`, `vested_le_total`,
`vested_nonneg`, `required_nonneg`, `vested_mono` — under the heading "Spec
arithmetic (`Spec.lean`, no UPLC)". They belong to no validator.
`scope.validators` is required with `minItems: 1` (`Assurance/Document.hs:156-158`
and the CIP meta-schema), so the only way to publish `vested_mono` is to
falsely scope it to `spendValidator`. The *definitions* it is about travel fine
as a fragment (§2.3); only the theorems have no home.

**Fix**: a `[scope: …]` clause in `PROPERTY`, and either an empty/absent
`scope.validators` or a `scope.fragments` alternative for
validator-independent properties. UAL syntax and the CIP schema.

**Blocking** for any contract with more than one validator, or with any property
about its pure model. Not blocking for the narrow slice-2 target, which can pass
`spend` and drop the six arithmetic theorems.

### 3.6 `imports` and ordering give a dependency DAG, not a file layout — not blocking, but it moves the acceptance criterion

Asked directly: ordering and `imports` **do** suffice for elaboration order.
Predicates within a fragment are joined in source order because a later block may
use an earlier one's definitions (`Build.hs:94`), fragments carry their
dependencies explicitly, and `findCycle` (`Build.hs:141-145`, `:160-189`)
rejects a cyclic set. That is everything a consumer needs to elaborate.

They do not determine *file layout*, and the reference's layout is not derivable
from anything in the pair. Its five modules are grouped by proof direction —
`Soundness.lean` / `Completeness.lean` / `Robustness.lean` — with definitions
living in the theorem module that first needs them (`Soundness.lean:28-139`
holds the context builders that `Completeness.lean:25` and `Robustness.lean:28`
then `open`). The pair has fragments (definitions) and properties (theorems)
keyed by *surface module*, and a Plinth contract has no "Soundness" module to
key off.

So the pair is sufficient to generate *a* correct project and insufficient to
generate *this* project. Spec §8.4 makes slice 2's acceptance test "a diff
against `contracts-library/formal/Formal/Vesting/Linear/`" — that criterion
cannot be met as written, and should become a semantic comparison, or the
reference should be relaid out to whatever layout the generator picks.

### 3.7 A property in a module with no `PREDICATE` block loses its `uses` — hazard, assurance

`Build.hs:114` sets `formalUses = [mname | Set.member mname fragmentIds]`, and
only modules with at least one predicate become fragments (`Build.hs:83`). A
surface module carrying `PROPERTY` blocks but no `PREDICATE` block therefore
emits properties with no `uses` at all, and a generator has nothing to import.

This is a hazard rather than a blocker: §2 routes around it by putting the
predicates and the properties in the same module, and that is enough, because
`uses: ["Vesting.Linear"]` plus that fragment's `imports` gives the transitive
closure. A gap the author avoids by module layout is a spec obligation, not a
generator failure.

The durable half is `Build.hs:99-101`'s own admission:

```haskell
    {- A property uses its own module's fragment, or nothing when that module
    produced none. It never names another: 'PropertyDecl' has no @uses@ field,
    so the annotation cannot ask for one. -}
```

**Fix**: document the obligation, or add a `uses` clause to `PROPERTY`.

---

## 4. Smaller items

- **`buildAssurance`'s scope argument is never checked against the blueprint.**
  `Build.hs:56-63` takes a bare `Text`; nothing validates it against
  `assuranceBlueprint`'s validator ids, unlike `attachUal`'s `missingErrors` and
  `orphanErrors` (`Ual/Resolve.hs`). `$(ualIdFor 'v)` is a call-site convention,
  not an enforced one, so a dangling `scope.validators` entry reaches the
  generator with no diagnostic.
- **Property id to Lean theorem name has no stated mapping.** `propertyIdent`
  permits `-` (`Assurance/Document.hs:154`) and `validator-arguments.golden.json`
  already uses `ticket-spend`, but a hyphen is illegal in a Lean identifier, and
  `foo-bar` collides with `foo_bar` under any sanitizer.
- **`asScott` is emittable with no consumer.** Spec §8.4 records that
  `CardanoLedgerApi` has no `IsScott`. Linear vesting is unaffected — its single
  argument is `asData` — but the format admits a value the generator must
  reject.
- **`formal.source` is a closed proposition**, so a theorem's binders and
  hypotheses have to be pre-quantified into the string (§2.4, §2.5) and the
  reference's hypothesis names (`hw`, `hlt`, `hge`) are lost. Only matters if a
  proof script wants to name them.
- **No tactic and no expected status.** Each reference theorem ends in `blaster`,
  `blaster (timeout: 10)` or `sorry`, and the choice is not uniform. The pair has
  no field for either; slice 3's `evidence` covers status, nothing covers the
  tactic.
- **`UPLC_DATA` cannot force a type into `definitions`.** `checkUplcData`
  (`Ual/TH.hs:182-186`) only checks the name is in scope. Whether `VestingDatum`
  reaches `definitions` depends entirely on the author writing
  `definitionRef @VestingDatum` and listing it in `deriveDefinitions` — the
  worked example lists only `BuiltinData`, which would give `#import_blueprints`
  no domain types at all.

---

## 5. What I could not determine

- **Whether `blaster` can symbolically execute `cekExecuteProgramWithBudget`.**
  No Lean toolchain here. This decides which branch of §3.2 the fix takes.
  `runStepsWithBudget`'s `decreasing_by sorry` (`CekMachine.lean:326-327`) is a
  reason for caution, and is plausibly why the reference uses the step-count
  machine in the first place.
- **§3.1 by reading, not by running.** I traced `emitStructType`'s guard and
  `emitSopType`'s `title` lookup in `BlueprintEncoding/Basic.lean` and compared
  Aiken's `definitions` against `Acme.golden.json`, but did not feed a
  Plinth-derived blueprint to `#import_blueprints` to watch it warn.
- **The reference does not build as checked out.** `Spec.lean:84-101` has
  `dGen`, `dWithTotal`, `dConcrete` and `dScript` commented out, while
  `Soundness.lean:186` and most of `Robustness.lean` use `dConcrete` and
  `dScript` (`Robustness.lean:30` even says they "come from `Spec` (opened
  above)"). §2 reconstructs `dConcrete` from the commented-out source and the
  "standard instance" of `README.md:20-28`.
- **No measured budget exists for this script**, in either repository, which is
  why §2.1's budget is zero.

---

## 6. Verdict

**The pair is not yet sufficient, and two of the three blockers are cheap now.**

| # | Gap | Document | Blocking |
| --- | --- | --- | --- |
| 3.1 | Plinth `definitions` cannot produce the datum/redeemer Lean types | blueprint | yes |
| 3.2 | `exCPU`/`exMem` versus the step bound | blueprint | no |
| 3.3 | No binding for the validator inside a formal statement | assurance + UAL | yes |
| 3.4 | Fragment `imports` drop non-fragments; no dialect or library versions | assurance | yes |
| 3.5 | Per-property scope: too coarse and too narrow | assurance + UAL | multi-validator only |
| 3.6 | `imports` give a DAG, not a file layout | neither | no |
| 3.7 | Properties in a predicate-less module lose `uses` | assurance | no (hazard) |

What the pair does carry, and carries well: the compiled program and its Lean
name; the applied-argument list, which for a V3 validator is exactly the arity
and encoding spec §9.1's wrapper needs; every definition the proofs are stated
against, as fragments, in an order and with a dependency DAG a consumer can
elaborate; and every theorem statement, with polarity intact, because
`formal.source` is verbatim text.

**The single most important thing to change is §3.1: get field and constructor
names into `definitions`.** Everything else on this list is a missing field in a
format that is still a draft. This one is a missing field in `plutus-tx`'s
`Schema` type, it is what the reference project's whole design rests on
(`Spec.lean:42-53` chose generated types over a hand-maintained mirror precisely
so the spec could not drift from the compiled schema), and Aiken already shows
the CIP-57-legal spelling. Until it is fixed, swapping this pipeline's
`plutus.json` in for the Aiken one turns a project that builds into one that
does not.
