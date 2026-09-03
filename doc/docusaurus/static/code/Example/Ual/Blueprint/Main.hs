-- BEGIN pragmas
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- END pragmas

{-| UAL annotations on a real, compiled validator, and a @main@ that writes the
two documents they produce: a CIP-0057 blueprint and a CIP assurance document.

The validator is the Cardano constitution script — the @Sorted@ engine of
@cardano-constitution@, statically configured with
@cardano-constitution\/data\/defaultConstitution.json@. It is genuinely compiled
to UPLC: @Cardano.Constitution.Validator.Sorted@ runs the Plinth plugin, and its
@defaultConstitutionCode@ is the resulting @PlutusTx.Code.CompiledCode@. The
blueprint's @compiledCode@ is @serialiseCompiledCode@ of that value, and its
@hash@ is what 'compiledValidator' derives from those same bytes, so both come
from this build rather than being stand-ins.

UAL annotations are ordinary Haskell block comments that open with a brace, a
dash and an at-sign. This module carries one of each kind:

  * @UPLC_DATA@ names a type that crosses the on-chain boundary;
  * @PREDICATE@ introduces definitions the properties are stated against;
  * @ONCHAIN@ gives a validator's applied-argument list, its Plutus version and
    its execution budget;
  * @PROPERTY@ states one behavioural claim, in English and formally.

== What the blueprint says about the interface

The constitution script takes one argument. Since Plutus V3 and CIP-0069 the
datum and redeemer are not separate arguments but live inside the
@ScriptContext@, so the single applied argument /is/ the context, passed as
@BuiltinData@. That is why the emitted @arguments@ array and the @redeemer@
object both @$ref@ the same @BuiltinData@ definition: @redeemer@ is CIP-0057's
required field, describing a value the ledger does supply and this validator
ignores (clause S04 of @cardano-constitution\/README.md@), while @arguments@ is
the UAL extension describing what the compiled program is actually applied to.
No @datum@ is emitted: the constitution script is not a spending validator.

The redeemer's @purpose@ set is empty, and so omitted. CIP-0057 offers
@spend@, @mint@, @withdraw@ and @publish@; a proposing script is none of them,
and picking the closest would be a claim the script does not support.

== Where the execution budget comes from

@[exCPU: 398773958, exMem: 2022856]@ is a measurement, not an estimate. It is
copied out of @sorted.golden.large.budget@, under
@cardano-constitution\/test\/Cardano\/Constitution\/Validator\/GoldenTests@,
which is the golden file of the @Golden\/BudgetLarge\/sorted@ test.
@Cardano.Constitution.Validator.defaultValidatorsWithCodes@ maps the name
@sorted@ to that module's @defaultConstitutionValidator@ and
@defaultConstitutionCode@, so that golden file is the one belonging to the code
embedded here. The test applies @defaultConstitutionCode@ to a fake proposing
@ScriptContext@ built by @Helpers.Guardrail.getFakeLargeParamsChange@: a
parameter-change proposal with an entry for every protocol parameter the test
suite's guardrail table covers. It runs the result on the CEK machine and
refuses to record a budget unless the run succeeded, so the figure is the cost
of /accepting/ a large proposal rather than of failing early on one.

Three things it is not:

  * It is measured with @defaultCekParametersForTesting@, the test cost model,
    which is not necessarily the cost model in force on a given chain.
  * It is the cost of that one proposal — the larger of the two contexts the
    golden tests cover, not a bound over all proposals.
  * Nothing in this pipeline checks it. @attachUal@ copies the annotation's
    budget into the blueprint, and @validatorBudget@ is explicit that it is not
    compared against 'validatorCompiled'. The golden file cannot drift from the
    code silently, because the test suite re-measures it on every run; but
    nothing compares the @ONCHAIN@ block below against the golden file, so
    keeping the two in step is the author's job. That is why the provenance is
    written down here.

== What the properties say, and what they do not

The five @PROPERTY@ blocks restate clauses of the constitution script's own
specification, in @cardano-constitution\/README.md@ under "Specification of
script implementation" — in the order they appear below: S01, S03 with S06 and
S07, S08, S06, and S05. They are stated, unverified claims: 'buildAssurance'
runs at build time, before any proof, so the emitted properties carry no
evidence records. The CIP names that case explicitly.

Two assumptions are written into the statements themselves rather than left
implicit. The @Sorted@ engine relies on the proposal's parameter map being
sorted and duplicate-free — ledger guarantees G02 and G01 — which the
@sortedOnKeys@ hypothesis stands for; and it relies on the configuration being
sorted too, which holds here because @defaultConstitutionConfig@ is derived from
the JSON file, whose format guarantees it by construction (README, "Current
script implementations").

Clause S02 — a @ParameterChange@ proposal that changes nothing — is deliberately
absent. The specification marks it @UNSPECIFIED@, and the test suite says its
own passing test for that case is regression testing of out-of-spec behaviour.
It is not a claim this document is entitled to make.

The @PREDICATE@ body is Lean source. Nothing in this repository parses or checks
it; the lexer reads the block verbatim and the assurance document carries it
through unchanged, for a prover to consume. -}
module Main where

-- BEGIN imports

import Cardano.Constitution.Validator.Sorted
  ( defaultConstitutionCode
  , defaultConstitutionValidator
  )
import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import PlutusLedgerApi.V3 (BuiltinData, serialiseCompiledCode)
import PlutusTx.Assurance
  ( AssurancePreamble (..)
  , blueprintRef
  , buildAssurance
  , writeAssurance
  )
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Validator
  ( compiledValidator
  , mkValidatorBlueprint
  , validatorCompiled
  , validatorDescription
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Blueprint.Write (writeBlueprint)
import PlutusTx.Prelude (BuiltinUnit)
import PlutusTx.Ual (ModuleUal, attachUal)
import PlutusTx.Ual.TH (ualIdFor, ualModule)

-- END imports
-- BEGIN annotated validator

{-@ UPLC_DATA BuiltinData @-}

{-@ PREDICATE
-- A `PlutusCore.Data` value: the encoding the ledger hands proposed protocol
-- parameter values over in. Left uninterpreted here.
axiom Data : Type

-- A ParameterChange proposal as the ledger encodes it: parameter id to
-- proposed value.
abbrev ChangedParams := List (Int × Data)

-- The governance action carried by the proposal under scrutiny. The
-- constitution script distinguishes exactly these three cases.
inductive GovAction where
  | parameterChange (cp : ChangedParams)
  | treasuryWithdrawals
  | otherAction

-- The two outcomes of a script run: it returns BuiltinUnit, or it errors.
-- README.md, "Legend": PASS with no checks left, versus FAIL, however the
-- failure is signalled.
inductive Verdict where
  | pass
  | fail

-- The outcome of the constitution script on a well-formed ProposingScript
-- ScriptContext whose ProposalProcedure carries the given governance action.
-- Nothing is said about a ScriptContext of any other shape: the script reaches
-- none of the three cases above without first decoding one.
axiom verdict : GovAction → Verdict

-- The parameter id has an entry in the constitution configuration compiled
-- into this script. Its negation is clause S08's "not found in the Config".
axiom configured : Int → Prop

-- The proposed value decodes at the type its configuration entry expects and
-- satisfies every rule that entry records for it. False for a value of the
-- wrong encoding or the wrong list length (S10, S11); true of every value when
-- the entry is `type: any` (S09).
axiom permitted : Int → Data → Prop

-- Every changed parameter is configured, and its proposed value is permitted.
def conforms (cp : ChangedParams) : Prop :=
  ∀ p ∈ cp, configured p.1 ∧ permitted p.1 p.2

-- Strictly increasing on the ids: the ledger guarantees the map is sorted (G02)
-- and duplicate-free (G01), and the Sorted engine assumes both.
def sortedOnKeys (cp : ChangedParams) : Prop :=
  List.Chain' (· < ·) (cp.map (·.1))
@-}

{-@ ONCHAIN [version: PlutusV3] [exCPU: 398773958, exMem: 2022856]
    constitutionValidator :: { BuiltinData : asData } -> BuiltinUnit
@-}

{-| The constitution script, as the ledger applies it.

'defaultConstitutionValidator' bound to a local name, with its signature written
out in arrows: the extraction splice reifies this name and counts the arrows in
its type, to check that the arity the @ONCHAIN@ block above declares is the
arity the binding actually has. -}
constitutionValidator :: BuiltinData -> BuiltinUnit
constitutionValidator = defaultConstitutionValidator

{-@ PROPERTY treasury_withdrawal_accepted
      "A treasury-withdrawals proposal is accepted with no further check."
    : verdict GovAction.treasuryWithdrawals = Verdict.pass
@-}

{-@ PROPERTY conforming_parameter_change_accepted
      "A proposal that changes at least one protocol parameter is accepted when
      every parameter it changes is configured in the constitution and the value
      proposed for it satisfies that parameter's rules."
    : ∀ (cp : ChangedParams), cp ≠ [] → sortedOnKeys cp → conforms cp →
        verdict (GovAction.parameterChange cp) = Verdict.pass
@-}

{-@ PROPERTY unconfigured_parameter_rejected
      "A proposal is rejected when it changes a protocol parameter the
      constitution configuration does not mention."
    : ∀ (cp : ChangedParams), sortedOnKeys cp → (∃ p ∈ cp, ¬ configured p.1) →
        verdict (GovAction.parameterChange cp) = Verdict.fail
@-}

{-@ PROPERTY out_of_range_parameter_rejected
      "A proposal is rejected when it sets a configured protocol parameter to a
      value the constitution's rules for that parameter forbid."
    : ∀ (cp : ChangedParams), sortedOnKeys cp →
        (∃ p ∈ cp, configured p.1 ∧ ¬ permitted p.1 p.2) →
        verdict (GovAction.parameterChange cp) = Verdict.fail
@-}

{-@ PROPERTY other_governance_action_rejected
      "A proposal is rejected when its governance action is neither a parameter
      change nor a treasury withdrawal."
    : verdict GovAction.otherAction = Verdict.fail
@-}

-- END annotated validator
-- BEGIN blueprint

myContractBlueprint :: ContractBlueprint
myContractBlueprint =
  MkContractBlueprint
    { contractId = Just "cardano-constitution"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "Cardano constitution script"
          , preambleDescription =
              Just
                "Checks that a governance proposal's changed protocol parameters \
                \conform to the constitution's configured ranges."
          , -- The version of the cardano-constitution package this script was
            -- taken from, not a version of this document.
            preambleVersion = "1.67.0.0"
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
              validatorId = Just $(ualIdFor 'constitutionValidator)
            , validatorTitle = "constitutionValidator"
            , validatorDescription =
                Just
                  "The Sorted engine, statically configured with \
                  \data/defaultConstitution.json."
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Redeemer"
                  , argumentDescription =
                      Just
                        "Supplied by the ledger and ignored by this validator \
                        \(clause S04). Since CIP-0069 it reaches the script \
                        \inside the ScriptContext, not as an argument of its own."
                  , -- None of CIP-0057's four purposes describes a proposing
                    -- script; an empty set omits the key.
                    argumentPurpose = Set.empty
                  , argumentSchema = definitionRef @BuiltinData
                  }
            , -- The real thing: UPLC produced by the Plinth plugin inside
              -- cardano-constitution, serialised, with the hash
              -- compiledValidator derives from those bytes.
              validatorCompiled =
                Just
                  ( compiledValidator
                      PlutusV3
                      (SBS.fromShort (serialiseCompiledCode defaultConstitutionCode))
                  )
            }
    , contractDefinitions = deriveDefinitions @'[BuiltinData]
    }

-- END blueprint
-- BEGIN assurance preamble

myAssurancePreamble :: AssurancePreamble
myAssurancePreamble =
  MkAssurancePreamble
    { assuranceTitle = "Cardano constitution script — UAL assurance"
    , assuranceDescription = Just "Generated from the UAL annotations in this module."
    , assuranceVersion = Just "1.0.0"
    , assuranceAuthors = ["Example Author <author@example.com>"]
    , -- YYYY-MM-DD; the assurance schema rejects any other shape.
      assuranceCreated = "2026-09-02"
    , assuranceLicense = Just "CC-BY-4.0"
    }

-- END assurance preamble

{- A top-level declaration splice that adds nothing. Its only job is to end the
declaration group above it: 'ualModule' reifies each ONCHAIN function to check
its arity, and GHC only puts a binding in the type environment once the group it
belongs to has been type-checked. Without this line the splice below fails with
"'constitutionValidator' is not in the type environment at a reify". -}
$(pure [])

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
main :: IO ()
main = do
  blueprint <- either (fail . show) pure (attachUal [contractUal] myContractBlueprint)
  writeBlueprint "plutus.json" blueprint
  ref <- blueprintRef "plutus.json" "plutus.json"
  doc <-
    either
      (fail . show)
      pure
      (buildAssurance myAssurancePreamble ref $(ualIdFor 'constitutionValidator) [contractUal])
  writeAssurance "assurance.json" doc

-- END main
