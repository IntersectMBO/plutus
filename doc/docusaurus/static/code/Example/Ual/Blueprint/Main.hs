-- BEGIN pragmas
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

-- END pragmas

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
  * @PROPERTY@ states one behavioural claim, in English and formally.

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
@BuiltinData@. That is what makes the two-entry @arguments@ array true, since
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

The two argument encodings differ, and both are load-bearing. The context is
@asData@: 'unsafeFromBuiltinData' decodes it from a @Data@ value. The parameter
is @asScott@, UAL's name for the other case, because 'PlutusTx.liftCodeDef' uses
the @Lift@ instance @makeLift@ generates, which builds a constructor application
in the compiler's own representation for algebraic data types rather than a
@Data@ value. UAL's design document is explicit that @asScott@ is emitted by this
slice but has no consumer yet.

== Where the execution budget comes from

@[exCPU: 10000000000, exMem: 16500000]@ is mainnet's per-transaction execution
limit: the @maxTxExecutionUnits@ pair, which @cardano-constitution@'s golden
tests name @maxTxExSteps@ and @maxTxExMem@ and point at a protocol-parameter
page for. The two figures were read on 2026-09-07 from a query for the
parameters in force on mainnet in epoch 654 (Koios's @epoch_params@ endpoint,
fields @max_tx_ex_steps@ and @max_tx_ex_mem@).

That makes it a ceiling rather than a measurement, which is what UAL defines
@exCPU@/@exMem@ to be: the most the compiled term is permitted to consume, under
the cost model in force, and not what it did consume on any particular run. Four
things it is not:

  * It is not this validator's cost. Nobody has measured that; this example
    contains no evaluation.
  * It is a /loose/ ceiling. The limit is per transaction and every script a
    transaction runs draws on the same allowance, so a single validator's true
    ceiling is lower by whatever else the transaction does.
  * It is not stable. The memory limit was 14000000 until a governance action
    raised it to the figure above, and further rises have been proposed since. A
    protocol parameter written into source goes stale, and nothing here notices.
  * Nothing in this pipeline checks it. @attachUal@ copies the annotation's
    budget into the blueprint, and 'validatorBudget' is explicit that it is not
    compared against 'validatorCompiled'.

== What the properties say, and what they do not

The four @PROPERTY@ blocks are stated, unverified claims. 'buildAssurance' runs
at build time, before any proof, so the emitted properties carry no evidence
records; the CIP names that case explicitly.

Each one is a claim about the behaviour described above, and each is stated over
the abstraction the @PREDICATE@ block introduces: a @Spend@ is the four facts the
validator reads out of its @ScriptContext@, and @verdict@ is its outcome on a
context those facts describe. Nothing is said about a @BuiltinData@ that does not
decode as a @ScriptContext@ at all — the script errors on one, but the model has
no name for it.

The @PREDICATE@ body is Lean source. Nothing in this repository parses or checks
it; the lexer reads the block verbatim and the assurance document carries it
through unchanged, for a prover to consume. Its @Value@ is uninterpreted apart
from the constant and the two operations the validator uses, which is why the
properties speak of @Value.geq@ and @Value.add@ rather than of amounts. -}
module Main where

-- BEGIN imports

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

-- END imports
-- BEGIN interface types

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

-- END interface types
-- BEGIN instances

{- 'makeIsDataSchemaIndexed' gives each type its @Data@ encoding *and* its
blueprint schema, with the constructor index pinned in the source. @Tranche@
comes first because @VestingParams@'s schema refers to it.

@makeLift@ is separate and also needed: 'PlutusTx.liftCodeDef' lifts a *Haskell*
value into a compiled program, which the @Data@ instances say nothing about. -}
$(makeIsDataSchemaIndexed ''Tranche [('MkTranche, 0)])
$(makeIsDataSchemaIndexed ''VestingParams [('MkVestingParams, 0)])
$(PlutusTx.makeLift ''Tranche)
$(PlutusTx.makeLift ''VestingParams)

-- END instances
-- BEGIN annotated validator

{-@ UPLC_DATA VestingParams @-}

{-@ UPLC_DATA Tranche @-}

{-@ UPLC_DATA BuiltinData @-}

{-@ PREDICATE
-- The ledger types the validator's parameter is built from, left
-- uninterpreted: nothing below needs to know what a key hash is.
axiom PubKeyHash : Type
axiom Value : Type

-- Value, with just what the validator uses of it: the empty value, addition,
-- and the pointwise ordering `geq` compares with.
axiom Value.zero : Value
axiom Value.add : Value → Value → Value
axiom Value.geq : Value → Value → Prop

-- POSIXTime: milliseconds since the Unix epoch, as the ledger counts them.
abbrev Time := Int

structure Tranche where
  deadline : Time
  amount : Value

structure VestingParams where
  owner : PubKeyHash
  tranche1 : Tranche
  tranche2 : Tranche

-- The four facts the validator reads out of its ScriptContext, and nothing
-- else: a context is described here exactly as far as the script inspects it.
structure Spend where
  -- `findOwnInput` succeeds: the script info says this run is spending an
  -- input, and the transaction has an input carrying that reference.
  ownInput : Bool
  -- The transaction's signatory list contains this key hash.
  signedBy : PubKeyHash → Bool
  -- The transaction's validity range lies entirely at or after this time.
  atOrAfter : Time → Bool
  -- The total value of the outputs that pay back to the address of the input
  -- being spent: `getContinuingOutputs`, summed.
  continuing : Value

-- The two outcomes of a script run: it returns BuiltinUnit, or it errors.
-- Which error, and whether anything was traced, is not distinguished.
inductive Verdict where
  | pass
  | fail

-- The outcome of the validator, on a well-formed ScriptContext whose facts are
-- the given ones. Nothing is said about a BuiltinData that does not decode as
-- a ScriptContext: the script errors on one, but no `Spend` describes it.
axiom verdict : VestingParams → Spend → Verdict

-- What one tranche requires to stay locked: nothing once its deadline is
-- reached in the sense above, its whole amount before that.
def Tranche.unvested (t : Tranche) (s : Spend) : Value :=
  if s.atOrAfter t.deadline then Value.zero else t.amount

-- What the whole schedule requires to stay locked.
def unvested (p : VestingParams) (s : Spend) : Value :=
  Value.add (p.tranche1.unvested s) (p.tranche2.unvested s)
@-}

{-@ ONCHAIN [version: PlutusV3] [exCPU: 10000000000, exMem: 16500000]
    vestingValidator :: { VestingParams : asScott }
                     -> { BuiltinData : asData }
                     -> BuiltinUnit
@-}

{-| Release what has vested; keep the rest locked.

The extraction splice reifies this name and counts the arrows in its type, to
check that the arity the @ONCHAIN@ block above declares is the arity the binding
actually has. -}
vestingValidator :: VestingParams -> BuiltinData -> BuiltinUnit
vestingValidator params ctxData =
  check
    ( traceIfFalse "the owner did not sign" (txSignedBy txInfo (vpOwner params))
        && traceIfFalse "unvested value was not left locked" (continuing `geq` unvested)
    )
  where
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
    : ∀ (p : VestingParams) (s : Spend),
        s.signedBy p.owner = false → verdict p s = Verdict.fail
@-}

{-@ PROPERTY unvested_value_stays_locked
      "A transaction is rejected when it leaves less value at the address of the
      input it spends than the total of the tranches that are not yet vested."
    : ∀ (p : VestingParams) (s : Spend),
        ¬ Value.geq s.continuing (unvested p s) → verdict p s = Verdict.fail
@-}

{-@ PROPERTY own_input_required
      "A transaction is rejected when the validator is not spending one of its
      inputs."
    : ∀ (p : VestingParams) (s : Spend),
        s.ownInput = false → verdict p s = Verdict.fail
@-}

{-@ PROPERTY conforming_spend_accepted
      "A transaction is accepted when it spends an input the validator guards,
      is signed by the owner, and leaves at least the total of the tranches that
      are not yet vested at the address of that input."
    : ∀ (p : VestingParams) (s : Spend),
        s.ownInput = true → s.signedBy p.owner = true →
          Value.geq s.continuing (unvested p s) → verdict p s = Verdict.pass
@-}

-- END annotated validator
-- BEGIN compiled code

{-| The validator as the Plinth plugin compiles it, with the parameter still to
apply.

This is what the blueprint publishes, so its @arguments@ array describes both
arguments. -}
vestingValidatorCode :: PlutusTx.CompiledCode (VestingParams -> BuiltinData -> BuiltinUnit)
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

'PlutusTx.applyCode' returns its failures rather than throwing them, which
'PlutusTx.unsafeApplyCode' does. It gives a @Left@ when the two programs cannot
be applied to one another: when either arrived without its PIR, or when applying
the two PIR programs fails. Both of these come from this build and carry their
PIR, so the @Left@ is not a case a reader has to worry about here; 'main' still
handles it, rather than discard an @Either@. -}
vestingInstance
  :: Haskell.Either Haskell.String (PlutusTx.CompiledCode (BuiltinData -> BuiltinUnit))
vestingInstance =
  vestingValidatorCode `PlutusTx.applyCode` PlutusTx.liftCodeDef exampleParams

-- END compiled code
-- BEGIN blueprint

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

-- END blueprint
-- BEGIN assurance preamble

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

-- END assurance preamble

{- A top-level declaration splice that adds nothing. Its only job is to end the
declaration group above it: 'ualModule' reifies each ONCHAIN function to check
its arity, and GHC only puts a binding in the type environment once the group it
belongs to has been type-checked. Without this line the splice below fails with
"'vestingValidator' is not in the type environment at a reify".

'Haskell.pure', not @pure@: this module imports 'PlutusTx.Prelude', whose @pure@
is the on-chain one and has no instance for the Template Haskell @Q@ monad. -}
$(Haskell.pure [])

-- BEGIN extraction

{-| Every UAL block of this module, read out of this file at compile time.

The splice must sit below every annotated binding and past the group boundary
above. Further declarations may follow, as 'main' does. -}
contractUal :: ModuleUal
contractUal = $(ualModule)

-- END extraction
-- BEGIN main

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

-- END main
