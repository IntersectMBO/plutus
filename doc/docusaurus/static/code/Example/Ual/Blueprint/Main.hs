{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

{-| UAL annotations on a compiled, parameterised validator, and a @main@ that
writes the two documents they produce: a CIP-0057 blueprint and a CIP assurance
document.

The validator is a two-tranche vesting script, written out in full below. It
lets an owner take vested funds out of the script address and requires whatever
is not yet vested to stay there. It is deliberately tiny: every claim the
@PROPERTY@ blocks make can be read off the bodies of 'vestingValidator' and
'trancheUnvested'.

UAL annotations are ordinary Haskell block comments that open with a brace, a
dash and an at-sign. This module carries all four kinds:

  * @UPLC_DATA@ names a type that crosses the on-chain boundary;
  * @PREDICATE@ introduces definitions the properties are stated against;
  * @ONCHAIN@ gives a validator's applied-argument list, its Plutus version and
    its execution budget;
  * @PROPERTY@ states one claim about the compiled program, in English and
    formally.

== The rules the validator enforces

Two checks, in this order.

  1. The transaction is signed by 'vpOwner'.
  2. The value the transaction pays back to the address of the input being spent
     is at least the total of the tranches that are not yet vested. A tranche is
     vested once the transaction's validity range lies entirely at or after its
     deadline, and then requires nothing; before that its whole amount must stay
     locked.

There is a third way to fail, which is not a check of ours:
'getContinuingOutputs' raises an error unless the validator is spending one of
the transaction's inputs, so a context of any other shape is rejected before
check 2 can be decided.

Nothing else is enforced. In particular the script does not look at a datum, does
not care which transaction outputs the released funds go to, and does not
distinguish the two tranches from a single tranche of their combined amount and
later deadline. A real vesting contract would want more; this one is sized to be
read, and to keep its stated properties short enough to check by eye.

== What this example demonstrates

  * A /parameterised/ validator. @VestingParams@ is a compile-time parameter, so
    the program takes two arguments and the blueprint's @arguments@ array has two
    entries.
  * A /record/ parameter with a record nested inside it, so @VestingParams@ and
    @Tranche@ reach the blueprint's @definitions@ with a @title@ on every field.
    Those titles are what lets a consumer generate a typed mirror of the
    parameter rather than treating it as opaque @Data@.
  * Genuinely compiled UPLC. 'vestingValidatorCode' is what the Plinth plugin
    produces from 'vestingValidator' in this build; the blueprint's
    @compiledCode@ is 'serialiseCompiledCode' of that value and its @hash@ is
    what 'compiledValidator' derives from those same bytes.

Note what puts a type in @definitions@: 'deriveDefinitions' and 'definitionRef',
not the @UPLC_DATA@ blocks. @UPLC_DATA@ only records the author's claim that a
type crosses the boundary — the splice checks that the name is in scope and
nothing more.

== What the blueprint says about the interface

@compiledCode@ is the /unapplied/ program: a function of a @VestingParams@ and a
@ScriptContext@, both @Data@-encoded. That is what makes the two-entry
@arguments@ array true, since
@arguments@ is "the ordered list of terms the compiled program is applied to",
and it is the shape the UAL design document's own worked example uses — a
parameterised script whose parameter is applied by the verifier's wrapper rather
than baked into the published bytes.

The parameter has to be applied before the script can be put on chain, and
CIP-0057's @parameters@ field is how a blueprint says so; 'vestingInstance' is
that step, for one example parameter set. The redeemer's @purpose@ is @spend@:
this is a spending validator. No @datum@ is emitted, because the validator reads
none — CIP-0057 makes @datum@ optional, and describing one would be a claim about
behaviour this code does not have. It does not make @redeemer@ optional, so that
field is there whether a validator reads a redeemer or not; this one does not,
and its description says so.

Both arguments are @asData@, and the parameter's entry is where the annotation
earns its keep. 'vestingValidator' takes it as a @BuiltinData@ and decodes it
with 'unsafeFromBuiltinData', exactly as it does the context, so the Haskell
signature alone says only "two @Data@ values". The @ONCHAIN@ block says which
type the first of them /is/ — @{ VestingParams : asData }@ — and that is what
reaches the blueprint as a @$ref@ into @definitions@. A consumer can therefore
give the argument its declared type rather than treat it as opaque bytes.

UAL's other encoding, @asScott@, names the case where a parameter is applied as a
constructor application in the compiler's own representation, which is what
'PlutusTx.liftCodeDef' produces from a @makeLift@-generated @Lift@ instance. This
example does not use it: nothing consumes @asScott@ yet, because there is no
Scott encoder to emit against, whereas @asData@ is what a verifier can act on
today.

== Where the execution budget comes from

@[steps: 2500]@ is a bound on abstract-machine steps, not a budget in cost-model
units. UAL accepts either, and this example uses steps because that is what a
consumer of the assurance document can currently act on: the machine it runs the
compiled program on takes a step count, and no budget-aware variant of it exists
yet. Declaring @[exCPU: n, exMem: n]@ instead would be the more meaningful
statement and would leave a consumer with nothing to convert it into.

2500 is the figure the hand-written proofs in @contracts-library/formal@ use for
a spending validator. It is a declared bound, chosen to be large enough to reach
a verdict — not a measurement, and nothing here measures one.

Five things this figure is not:

  * It is not this validator's cost. Nobody has measured that; this example
    contains no evaluation.
  * It is not comparable to the ledger's limits. Those are in cost-model units
    per transaction; a step count is specific to one abstract machine and has no
    exchange rate with them.
  * It is not a substitute for a budget. 'PlutusTx.Blueprint.Validator.MkStepBudget'
    says so in as many words, and 'MkExecutionBudget' stays preferred wherever a
    consumer can use it.
  * It is not stable across machines. A different evaluator, or a change to this
    one's step accounting, moves it.
  * Nothing in this pipeline checks it. @attachUal@ copies the annotation's
    budget into the blueprint, and 'validatorBudget' is explicit that it is not
    compared against 'validatorCompiled'.

== What the properties say, and what they do not

The four @PROPERTY@ blocks are stated, unverified claims. 'buildAssurance' runs
at build time, before any proof, so the emitted properties carry no evidence
records; the CIP names that case explicitly.

Each is stated against the script itself, not against a model of it. The name
@vestingValidator@ in a property denotes the compiled program: a consumer reads
@validators[0].id@ and the @arguments@ list out of the blueprint and emits a
wrapper that applies the program to the encoded arguments and runs it, so
@isSuccessful (vestingValidator …)@ is a claim about the UPLC in @compiledCode@.
That is what makes these properties falsifiable — a claim about an axiom standing
in for the script would be provable whether or not the script behaved that way.

Both arguments being @asData@ is what makes that wrapper emittable at all, and
the parameter reaches it as a @VestingParams@. Its second binder keeps the
declared type of the second argument, @BuiltinData@, so a property that
quantifies over a @ScriptContext@ has to encode it: @toLedgerData ctx@ is the
ledger's own @Data@ encoding, which is what the ledger hands the script. Doing
that in the property rather than hiding it in the wrapper is deliberate — the
encoding is part of what is being claimed.

Everything else the properties mention comes from somewhere concrete too:
@VestingParams@, @Tranche@ and their field names are generated from this
blueprint's @definitions@; @ScriptContext@, @POSIXTime@, @Value@, @txSignedBy@
and @findOwnInput@ are @CardanoLedgerApi.V3@'s. The @PREDICATE@ block therefore
carries only what is genuinely specification — the vesting schedule — rather than
re-declaring types the blueprint already describes.

Being @CardanoLedgerApi@'s and not this module's, they take their own argument
order and their own types, neither always Plinth's.

  * @txSignedBy@ is @txSignedBy pk tx@, the reverse of Plinth's
    @txSignedBy tx pk@, so the properties below read the other way round from
    'vestingValidator'.
  * @txInfoValidRange@ is kept at @Data@, so the deadline premise goes through
    @txRangeStartsAt@, which decodes it. That premise says the range /begins/ at
    @now@, not merely that it lies at or after it: the weaker reading would let
    two different @now@ satisfy it and select different schedules, which is
    enough to make @conforming_spend_accepted@ false.
  * A blueprint types a @Value@ as a map of currency symbol to token map, so the
    generated @trancheAmount@ and @CardanoLedgerApi@'s @Value@ are different
    Lean types carrying the same information. @ofTypedValue@ crosses between
    them.
  * @Value@ is an alias for a list, which already has a lexicographic @≤@. An
    @unvested@ premise written with @≥@ would elaborate — to list ordering, not
    to value comparison — so the properties call @geq@ by name.

@continuingValue@ is an @Option@, and binding it with @= some v@ does double
duty: it names the value and it says the validator has an own input. That is why
@conforming_spend_accepted@ needs no separate @findOwnInput@ premise, while
@own_input_required@ is still a claim of its own about the @none@ case.

All five elaborate and reach a prover. Only the fifth is discharged. Given the
document and the blueprint, blaster settles @malformed_context_rejected@ in
under a minute; each of the other four was given at least eight minutes, one of
them twelve, and none of the four returned a verdict. That is one machine and
one version of the prover, but the gap is not a close call.

The reason is visible in the statements. The first four quantify over a
@ScriptContext@ and pass @toLedgerData ctx@, so discharging one means relating
@CardanoLedgerApi@'s model of a context to what the compiled program's own
decoder makes of the same bytes, across 2500 steps of a machine walking the
transaction's inputs and outputs. That is a functional-correctness argument
about the decoder, arrived at sideways. The fifth passes a @Data@ that decodes
as nothing, so the program fails early and the search stays small.

None of this is recorded in @assurance.json@: 'buildAssurance' runs at build
time, before any prover, so every property is emitted without an @evidence@
record — including the one that would pass. Evidence is a consumer's to add.

The fifth property is also the malformed-@Data@ case, which the other four
structurally cannot reach: they range over encoded @ScriptContext@s, so every
context they quantify over decodes by construction. @own_input_required@ is a
different claim — a well-formed context whose purpose does not resolve to one of
the transaction's inputs.

One thing all five lean on that is not yet written down: the convention that a
validator's id denotes the applied wrapper inside a property is proposed rather
than specified in UAL. It is recorded in
@docs/superpowers/ual-doc-corrections.md@.

The @PREDICATE@ and @PROPERTY@ bodies are Lean source. Nothing in this repository
parses or checks them; the lexer reads each block verbatim and the assurance
document carries it through unchanged, for a prover to consume. -}
module Main where

import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Interval (contains)
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V3
  ( POSIXTime (..)
  , POSIXTimeRange
  , PubKeyHash
  , ScriptContext (..)
  , TxInfo (..)
  , TxOut (..)
  , Value
  , from
  , geq
  , serialiseCompiledCode
  )
import PlutusLedgerApi.V3.Contexts (getContinuingOutputs, txSignedBy)
import PlutusTx qualified
import PlutusTx.Assurance
  ( AssurancePreamble (..)
  , blueprintRef
  , buildAssurance
  , writeAssurance
  )
import PlutusTx.Blueprint
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.List (foldr)
import PlutusTx.Prelude
import PlutusTx.Ual (ModuleUal, attachUal)
import PlutusTx.Ual.TH (ualIdFor, ualModule)
import Prelude qualified as Haskell

{-| One instalment of the schedule.

Its two fields are what the blueprint's @definitions@ entry for @Tranche@ is
named after: 'makeIsDataSchemaIndexed' reads the record's field names off the
declaration, so the emitted schema carries them with no annotation here. -}
data Tranche = MkTranche
  { trancheDeadline :: POSIXTime
  {-^ Vested once the transaction's validity range lies entirely at or after
  this time. -}
  , trancheAmount :: Value
  -- ^ What must stay locked until then.
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

{-| The validator's compile-time parameter: who may take the funds, and on what
schedule.

A nested record, so the blueprint needs both this definition and @Tranche@'s, and
the @vpTranche1@/@vpTranche2@ fields are @$ref@s into the latter. -}
data VestingParams = MkVestingParams
  { vpOwner :: PubKeyHash
  -- ^ The only key that may spend from the script address.
  , vpTranche1 :: Tranche
  , vpTranche2 :: Tranche
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

{- 'makeIsDataSchemaIndexed' gives each type its @Data@ encoding *and* its
blueprint schema, with the constructor index pinned in the source. @Tranche@
comes first because @VestingParams@'s schema refers to it.

These two splices are all this module needs. @makeLift@ would be the other half
if the parameter were applied as a constructor application in the compiler's own
representation, but it is applied as @Data@ here, and the @Data@ encoding is
exactly what 'makeIsDataSchemaIndexed' provides. -}
$(makeIsDataSchemaIndexed ''Tranche [('MkTranche, 0)])
$(makeIsDataSchemaIndexed ''VestingParams [('MkVestingParams, 0)])

{-@ UPLC_DATA VestingParams @-}

{-@ UPLC_DATA Tranche @-}

{-@ UPLC_DATA BuiltinData @-}

{-@ PREDICATE
-- What one tranche still requires to stay locked, at a time. `Value`,
-- `POSIXTime`, `null`, `merge` and `ofTypedValue` are CardanoLedgerApi.V3's;
-- `Tranche` and its field names come from this blueprint's `definitions`.
--
-- `ofTypedValue` is the crossing between the two. A blueprint describes a
-- Value as a map of currency symbol to token map, so the generated
-- `trancheAmount` has that type; the ledger's Value keeps its keys as Data.
def trancheUnvested (t : Tranche) (now : POSIXTime) : Value :=
  if now >= t.trancheDeadline then null else ofTypedValue t.trancheAmount

-- What the whole schedule requires to stay locked.
def unvested (p : VestingParams) (now : POSIXTime) : Value :=
  merge (trancheUnvested p.vpTranche1 now) (trancheUnvested p.vpTranche2 now)
@-}

{-@ ONCHAIN [version: PlutusV3] [steps: 2500]
    vestingValidator :: { VestingParams : asData }
                     -> { BuiltinData : asData }
                     -> BuiltinUnit
@-}

{-| Release what has vested; keep the rest locked.

Both arguments arrive as @Data@ and are decoded here. The parameter is a
@VestingParams@ — that is what the @ONCHAIN@ block above and the blueprint's
@parameters@ both say, and it is what the deployer applies — but it crosses the
on-chain boundary in its @Data@ encoding, so the Haskell type at that position is
@BuiltinData@.

The extraction splice reifies this name and counts the arrows in its type, to
check that the arity the @ONCHAIN@ block above declares is the arity the binding
actually has. It compares arities and nothing else, which is what lets the
annotation name @VestingParams@ where the signature says @BuiltinData@. -}
vestingValidator :: BuiltinData -> BuiltinData -> BuiltinUnit
vestingValidator paramsData ctxData =
  check
    ( traceIfFalse "the owner did not sign" (txSignedBy txInfo (vpOwner params))
        && traceIfFalse "unvested value was not left locked" (continuing `geq` unvested)
    )
  where
    params :: VestingParams
    params = unsafeFromBuiltinData paramsData

    ctx :: ScriptContext
    ctx = unsafeFromBuiltinData ctxData

    txInfo :: TxInfo
    txInfo = scriptContextTxInfo ctx

    {- The value paid back to the address of the input being spent.
    'getContinuingOutputs' raises an error if this validator is not spending one
    of the transaction's inputs, so demanding this rejects such a context. -}
    continuing :: Value
    continuing = foldr (\o acc -> txOutValue o + acc) zero (getContinuingOutputs ctx)

    unvested :: Value
    unvested =
      trancheUnvested (vpTranche1 params) (txInfoValidRange txInfo)
        + trancheUnvested (vpTranche2 params) (txInfoValidRange txInfo)
{-# INLINEABLE vestingValidator #-}

{-| What a tranche still requires to stay locked, given a transaction's validity
range.

@from d@ is the interval from @d@ onwards, so @contains@ asks whether the whole
of @range@ lies at or after the deadline. A range that merely overlaps the
deadline does not vest the tranche: the transaction could be accepted at a time
before it. -}
trancheUnvested :: Tranche -> POSIXTimeRange -> Value
trancheUnvested tranche range =
  if from (trancheDeadline tranche) `contains` range
    then zero
    else trancheAmount tranche
{-# INLINEABLE trancheUnvested #-}

{-@ PROPERTY owner_signature_required
      "A transaction that the owner has not signed is rejected."
    : ∀ (p : VestingParams) (ctx : ScriptContext),
        ¬ txSignedBy p.vpOwner ctx.scriptContextTxInfo →
          ¬ isSuccessful (vestingValidator p (toLedgerData ctx))
@-}

{-@ PROPERTY unvested_value_stays_locked
      "A transaction is rejected when it leaves less value at the address of the
      input it spends than the total of the tranches that are not yet vested."
    : ∀ (p : VestingParams) (ctx : ScriptContext) (now : POSIXTime) (v : Value),
        txRangeStartsAt now ctx.scriptContextTxInfo.txInfoValidRange →
          continuingValue ctx = some v →
            ¬ geq v (unvested p now) →
              ¬ isSuccessful (vestingValidator p (toLedgerData ctx))
@-}

{-@ PROPERTY own_input_required
      "A transaction is rejected when the validator is not spending one of its
      inputs."
    : ∀ (p : VestingParams) (ctx : ScriptContext),
        findOwnInput ctx = none →
          ¬ isSuccessful (vestingValidator p (toLedgerData ctx))
@-}

{-@ PROPERTY conforming_spend_accepted
      "A transaction is accepted when it spends an input the validator guards,
      is signed by the owner, and leaves at least the total of the tranches that
      are not yet vested at the address of that input."
    : ∀ (p : VestingParams) (ctx : ScriptContext) (now : POSIXTime) (v : Value),
        txSignedBy p.vpOwner ctx.scriptContextTxInfo →
          txRangeStartsAt now ctx.scriptContextTxInfo.txInfoValidRange →
            continuingValue ctx = some v →
              geq v (unvested p now) →
                isSuccessful (vestingValidator p (toLedgerData ctx))
@-}

{-@ PROPERTY malformed_context_rejected
      "A transaction is rejected when what reaches the validator in place of a
      script context does not decode as one."
    : ∀ (p : VestingParams), ¬ isSuccessful (vestingValidator p (Data.I 0))
@-}

{-| The validator as the Plinth plugin compiles it, with the parameter still to
apply.

This is what the blueprint publishes, so its @arguments@ array describes both
arguments. -}
vestingValidatorCode :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinUnit)
vestingValidatorCode = $$(PlutusTx.compile [||vestingValidator||])

{-| One parameter set, to show the schedule the types describe.

The owner is a made-up 28 bytes, the length of a @PubKeyHash@, written as the 56
hex characters its 'Data.String.IsString' instance decodes. The amounts are
1500000 and 2500000 lovelace — 1.5 and 2.5 ADA — and the deadlines are
2026-01-01 and 2026-07-01, in milliseconds since the Unix epoch as a
@POSIXTime@ counts them.

Nothing here is on chain: it is an ordinary Haskell value, lifted below. -}
exampleParams :: VestingParams
exampleParams =
  MkVestingParams
    { vpOwner = "00112233445566778899aabbccddeeff00112233445566778899aabb"
    , vpTranche1 =
        MkTranche
          { trancheDeadline = POSIXTime 1767225600000
          , trancheAmount = Value.singleton Value.adaSymbol Value.adaToken 1500000
          }
    , vpTranche2 =
        MkTranche
          { trancheDeadline = POSIXTime 1782864000000
          , trancheAmount = Value.singleton Value.adaSymbol Value.adaToken 2500000
          }
    }

{-| The script a deployer would put on chain: 'vestingValidatorCode' with
'exampleParams' applied.

This is the step CIP-0057's @parameters@ field exists to announce. Applying a
parameter changes the program and therefore its hash, so this is /not/ the script
the blueprint describes; it is what one instance of it looks like.

'toBuiltinData' first, because the program's first argument is a @Data@ value:
that is what @{ VestingParams : asData }@ declares and what 'vestingValidator'
decodes. Lifting @exampleParams@ itself would need the @Lift@ instance
@makeLift@ generates and would build the wrong thing here.

'PlutusTx.applyCode' returns its failures rather than throwing them, which
'PlutusTx.unsafeApplyCode' does. It gives a @Left@ when the two programs cannot
be applied to one another: when either arrived without its PIR, or when applying
the two PIR programs fails. Both of these come from this build and carry their
PIR, so the @Left@ is not a case a reader has to worry about here; 'main' still
handles it, rather than discard an @Either@. -}
vestingInstance
  :: Haskell.Either Haskell.String (PlutusTx.CompiledCode (BuiltinData -> BuiltinUnit))
vestingInstance =
  vestingValidatorCode `PlutusTx.applyCode` PlutusTx.liftCodeDef (toBuiltinData exampleParams)

myContractBlueprint :: ContractBlueprint
myContractBlueprint =
  MkContractBlueprint
    { contractId = Just "two-tranche-vesting"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "Two-tranche vesting"
          , preambleDescription =
              Just
                "Releases each tranche once the spending transaction's validity \
                \range lies entirely at or after that tranche's deadline, and \
                \requires the rest to stay locked."
          , preambleVersion = "1.0.0"
          , -- Must agree with the ONCHAIN block's [version: …], or attachUal
            -- reports a VersionMismatch.
            preamblePlutusVersion = PlutusV3
          , preambleLicense = Just "Apache-2.0"
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { -- ualIdFor derives the id from the Haskell name, so the blueprint
              -- entry and the ONCHAIN block cannot drift apart: renaming the
              -- function is a compile error rather than an unmatched id.
              validatorId = Just $(ualIdFor 'vestingValidator)
            , validatorTitle = "vestingValidator"
            , validatorDescription =
                Just "Lets the owner take vested funds and keeps the rest locked."
            , validatorParameters =
                [ MkParameterBlueprint
                    { parameterTitle = Just "VestingParams"
                    , parameterDescription =
                        Just
                          "The owner and the two-tranche schedule. Must be \
                          \applied to the compiled code before it can be put on \
                          \chain."
                    , parameterPurpose = Set.singleton Spend
                    , parameterSchema = definitionRef @VestingParams
                    }
                ]
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Redeemer"
                  , argumentDescription =
                      Just
                        "This validator does not read the redeemer. Since \
                        \CIP-0069 the redeemer is not an argument of its own: it \
                        \arrives inside the ScriptContext, which is the \
                        \BuiltinData the program is applied to and which the \
                        \validator does read."
                  , argumentPurpose = Set.singleton Spend
                  , argumentSchema = definitionRef @BuiltinData
                  }
            , -- No datum: this validator reads none. CIP-0057 makes the field
              -- optional, and leaving it out says so.
              validatorCompiled =
                Just
                  ( compiledValidator
                      PlutusV3
                      (SBS.fromShort (serialiseCompiledCode vestingValidatorCode))
                  )
            }
    , -- Tranche is listed as well as VestingParams: it would be pulled in
      -- transitively anyway, and naming it makes the $ref that points at it
      -- impossible to leave dangling.
      contractDefinitions = deriveDefinitions @'[VestingParams, Tranche, BuiltinData]
    }

myAssurancePreamble :: AssurancePreamble
myAssurancePreamble =
  MkAssurancePreamble
    { assuranceTitle = "Two-tranche vesting — UAL assurance"
    , assuranceDescription = Just "Generated from the UAL annotations in this module."
    , assuranceVersion = Just "1.0.0"
    , assuranceAuthors = ["Romain Soulat <romain.soulat@iohk.io>"]
    , assuranceCreated = "2026-09-07"
    , assuranceLicense = Just "CC-BY-4.0"
    }

{- A top-level declaration splice that adds nothing. Its only job is to end the
declaration group above it: 'ualModule' reifies each ONCHAIN function to check
its arity, and GHC only puts a binding in the type environment once the group it
belongs to has been type-checked. Without this line the splice below fails with
"'vestingValidator' is not in the type environment at a reify".

'Haskell.pure', not @pure@: this module imports 'PlutusTx.Prelude', whose @pure@
is the on-chain one and has no instance for the Template Haskell @Q@ monad. -}
$(Haskell.pure [])

{-| Every UAL block of this module, read out of this file at compile time.

The splice must sit below every annotated binding and past the group boundary
above. Further declarations may follow, as 'main' does. -}
contractUal :: ModuleUal
contractUal = $(ualModule)

{-| Write @plutus.json@ and @assurance.json@ into the current directory.

The order is forced: 'blueprintRef' hashes the blueprint bytes on disk, so the
blueprint must already have been written, and the assurance document embeds that
hash. -}
main :: Haskell.IO ()
main = do
  _ <- either Haskell.fail Haskell.pure vestingInstance
  blueprint <- either die Haskell.pure (attachUal [contractUal] myContractBlueprint)
  writeBlueprint "plutus.json" blueprint
  ref <- blueprintRef "plutus.json" "plutus.json"
  doc <-
    either
      die
      Haskell.pure
      (buildAssurance myAssurancePreamble ref $(ualIdFor 'vestingValidator) [contractUal])
  writeAssurance "assurance.json" doc
  where
    die :: Haskell.Show e => e -> Haskell.IO a
    die = Haskell.fail . Haskell.show
