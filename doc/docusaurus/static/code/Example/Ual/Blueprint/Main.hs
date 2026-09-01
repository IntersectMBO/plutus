-- BEGIN pragmas
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- END pragmas

{-| A contract module annotated with UAL, and a @main@ that writes the two
documents the annotations produce: a CIP-0057 blueprint and a CIP assurance
document.

UAL annotations are ordinary Haskell block comments that open with a brace, a
dash and an at-sign. This module carries one of each kind:

  * @UPLC_DATA@ names a type that crosses the on-chain boundary;
  * @PREDICATE@ introduces definitions the properties are stated against;
  * @ONCHAIN@ gives a validator's applied-argument list, its Plutus version and
    its execution budget;
  * @PROPERTY@ states one behavioural claim, in English and formally.

Nothing here is compiled to UPLC: the point of the example is the annotation
pipeline, so the validator is plain Haskell. The execution budget in the
@ONCHAIN@ block is therefore a stand-in for one you would measure against your
own compiled script. -}
module Main where

-- BEGIN imports

import Data.Set qualified as Set
import GHC.Generics (Generic)
import PlutusTx.Assurance
  ( AssurancePreamble (..)
  , blueprintRef
  , buildAssurance
  , writeAssurance
  )
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Blueprint.Validator
  ( mkValidatorBlueprint
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Blueprint.Write (writeBlueprint)
import PlutusTx.Ual (ModuleUal, attachUal)
import PlutusTx.Ual.TH (ualIdFor, ualModule)

-- END imports
-- BEGIN interface types

newtype Ticket = MkTicket {ticketValue :: Integer}
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeIsDataSchemaIndexed ''Ticket [('MkTicket, 0)])

-- END interface types
-- BEGIN annotated validator

{-@ UPLC_DATA Ticket @-}

{-@ PREDICATE
def ticketOk (t : Ticket) : Prop := t.value > 0
@-}

{-@ ONCHAIN [version: PlutusV3] [exCPU: 1883313, exMem: 12342]
    ticketSpend :: { Ticket : asData }
                -> { [Integer] : asData }
                -> Bool
@-}
ticketSpend :: Ticket -> [Integer] -> Bool
ticketSpend ticket spent = ticketValue ticket > 0 && ticketValue ticket `notElem` spent

{-@ PROPERTY accepted_ticket_is_ok
      "Every ticket the validator accepts has a positive value."
    : ∀ (t : Ticket) (spent : [Integer]), ticketSpend t spent → ticketOk t
@-}

-- END annotated validator
-- BEGIN blueprint

myContractBlueprint :: ContractBlueprint
myContractBlueprint =
  MkContractBlueprint
    { contractId = Just "ticket-contract"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "Ticket contract"
          , preambleDescription = Just "Spends a ticket that has not been spent before."
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
              validatorId = Just $(ualIdFor 'ticketSpend)
            , validatorTitle = "ticketSpend"
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Just "Ticket"
                  , argumentDescription = Nothing
                  , argumentPurpose = Set.singleton Purpose.Spend
                  , argumentSchema = definitionRef @Ticket
                  }
            }
    , contractDefinitions = deriveDefinitions @[Ticket, [Integer]]
    }

-- END blueprint
-- BEGIN assurance preamble

myAssurancePreamble :: AssurancePreamble
myAssurancePreamble =
  MkAssurancePreamble
    { assuranceTitle = "Ticket contract — UAL assurance"
    , assuranceDescription = Just "Generated from the UAL annotations in this module."
    , assuranceVersion = Just "1.0.0"
    , assuranceAuthors = ["Example Author <author@example.com>"]
    , -- YYYY-MM-DD; the assurance schema rejects any other shape.
      assuranceCreated = "2026-08-24"
    , assuranceLicense = Just "CC-BY-4.0"
    }

-- END assurance preamble

{- A top-level declaration splice that adds nothing. Its only job is to end the
declaration group above it: 'ualModule' reifies each ONCHAIN function to check
its arity, and GHC only puts a binding in the type environment once the group it
belongs to has been type-checked. Without this line the splice below fails with
"'ticketSpend' is not in the type environment at a reify". -}
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
      (buildAssurance myAssurancePreamble ref $(ualIdFor 'ticketSpend) [contractUal])
  writeAssurance "assurance.json" doc

-- END main
