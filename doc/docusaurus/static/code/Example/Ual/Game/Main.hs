{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fno-strictness #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.0.0 #-}

module Main where

import Data.ByteString.Short qualified as SBS
import Data.Set qualified as Set
import PlutusLedgerApi.V2 (serialiseCompiledCode)
import PlutusTx qualified
import PlutusTx.Assurance
import PlutusTx.Blueprint
import PlutusTx.Prelude
import PlutusTx.Ual (ModuleUal)
import PlutusTx.Ual.TH (ualIdFor, ualModule)
import System.Environment (getArgs)
import Prelude qualified as Haskell

-- The isGoodGuess rule from plutus-apps' Plutus.Contracts.Game.Alonzo:
-- actual == sha2_256 guess. This example ports the on-chain rule to current
-- Plinth and an explicit Data boundary; it does not claim to rebuild the old
-- off-chain application or its address-diversifying GameParam.
{-@ ONCHAIN [version: PlutusV2] [steps: 500, semantics: D]
    gameValidator :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit
@-}
{-# INLINEABLE gameValidator #-}
gameValidator :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit
gameValidator datum redeemer _ =
  check
    ((unsafeFromBuiltinData datum :: BuiltinByteString) == sha2_256 (unsafeFromBuiltinData redeemer))

{-@ PREDICATE
def hashMatches (actual guess : ByteString) : Prop :=
  actual = PlutusCore.Crypto.Hash.sha2_256 guess
@-}

{-@ PROPERTY [scope: gameValidator] correct_guess
    "A guess whose hash matches the datum terminates successfully for every context."
  : ∀ (actual guess : ByteString) (ctx : Data), hashMatches actual guess →
      isSuccessful (gameValidator (Data.B actual) (Data.B guess) ctx)
@-}

{-@ PROPERTY [scope: gameValidator] wrong_guess
    "A guess whose hash differs from the datum fails script evaluation for every context."
  : ∀ (actual guess : ByteString) (ctx : Data), ¬ hashMatches actual guess →
      isUnsuccessful (gameValidator (Data.B actual) (Data.B guess) ctx)
@-}

{-@ PROPERTY [scope: gameValidator] malformed_datum
    "An integer datum fails to decode as the stored hash, for every redeemer and context."
  : ∀ (r ctx : Data), isUnsuccessful (gameValidator (Data.I 0) r ctx)
@-}

code :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit)
code = $$(PlutusTx.compile [||gameValidator||])

blueprint :: ContractBlueprint
blueprint =
  MkContractBlueprint
    { contractId = Just "ual-game"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "Guessing game — plutus-apps rule"
          , preambleDescription = Just "Current-Plinth port of the Game.isGoodGuess on-chain rule."
          , preambleVersion = "1.0.0"
          , preamblePlutusVersion = PlutusV2
          , preambleLicense = Just "Apache-2.0"
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just $(ualIdFor 'gameValidator)
            , validatorTitle = "Guess the secret"
            , validatorDatum =
                Just (MkArgumentBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @BuiltinData))
            , validatorRedeemer =
                MkArgumentBlueprint Nothing Nothing (Set.singleton Spend) (definitionRef @BuiltinData)
            , validatorCompiled = Just (compiledValidator PlutusV2 (SBS.fromShort (serialiseCompiledCode code)))
            }
    , contractDefinitions = deriveDefinitions @'[BuiltinData]
    }

$(Haskell.pure [])
annotations :: ModuleUal
annotations = $(ualModule)

main :: Haskell.IO ()
main = do
  args <- getArgs
  environment <- case args of
    [path] -> Haskell.pure path
    _ -> Haskell.fail "usage: example-ual-game ENVIRONMENT.json"
  let preamble =
        MkAssurancePreamble
          { assuranceTitle = "Guessing game assurance"
          , assuranceDescription = Just "Generated claims about the compiled guessing-game rule."
          , assuranceVersion = Just "1.0.0"
          , assuranceAuthors = ["Plutus contributors"]
          , assuranceCreated = "2026-09-29"
          , assuranceLicense = Just "Apache-2.0"
          }
  writeInterfaceBundle environment preamble "gameValidator" [annotations] blueprint
