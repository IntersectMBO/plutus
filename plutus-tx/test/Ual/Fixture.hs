{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| A module with real UAL annotations, used to test that @$(ualModule)@ reads
its own source. Everything here is a fixture; nothing is a real contract. -}
module Ual.Fixture (Ticket (..), fixtureUal, fixtureContract, tests) where

import Prelude

import Data.Set qualified as Set
import Data.Text qualified as Text
import GHC.Generics (Generic)
import PlutusTx.Blueprint.Argument (ArgumentBlueprint (..))
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Contract (ContractBlueprint (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef, deriveDefinitions)
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Blueprint.Preamble (Preamble (..))
import PlutusTx.Blueprint.Purpose qualified as Purpose
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Blueprint.Schema.Annotation (emptySchemaInfo)
import PlutusTx.Blueprint.Validator
  ( ExecutionBudget (..)
  , mkValidatorBlueprint
  , validatorId
  , validatorRedeemer
  , validatorTitle
  )
import PlutusTx.Ual
  ( ModuleUal (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  )
import PlutusTx.Ual.TH (ualIdFor, ualModule)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

newtype Ticket = MkTicket Integer
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

{-| Hand-written rather than TH-derived: the fixture only needs *some* schema for
'Ticket', and this keeps the module's Template Haskell down to the splice under
test. -}
instance HasBlueprintSchema Ticket referencedTypes where
  schema = SchemaBuiltInInteger emptySchemaInfo

{-@ UPLC_DATA Ticket @-}

{-@ PREDICATE
def ticketOk (t : Integer) : Prop := t > 0
@-}

{-@ ONCHAIN [version: PlutusV3] [exCPU: 1883313, exMem: 12342]
    ticketSpend :: { Ticket : asData }
                -> { [Integer] : asData }
                -> ()
@-}
ticketSpend :: Ticket -> [Integer] -> ()
ticketSpend _ _ = ()

{-@ PROPERTY ticket_ok
      "A ticket with a positive value is accepted."
    : ∀ (t : Integer) (xs : List Integer), ticketOk t → isSuccessful (ticketSpend t xs)
@-}

fixtureContract :: ContractBlueprint
fixtureContract =
  MkContractBlueprint
    { contractId = Just "ual-fixture"
    , contractPreamble =
        MkPreamble
          { preambleTitle = "UAL Fixture"
          , preambleDescription = Nothing
          , preambleVersion = "1.0.0"
          , preamblePlutusVersion = PlutusV3
          , preambleLicense = Nothing
          }
    , contractValidators =
        Set.singleton
          mkValidatorBlueprint
            { validatorId = Just $(ualIdFor 'ticketSpend)
            , validatorTitle = "ticketSpend"
            , validatorRedeemer =
                MkArgumentBlueprint
                  { argumentTitle = Nothing
                  , argumentDescription = Nothing
                  , argumentPurpose = Set.singleton Purpose.Spend
                  , argumentSchema = definitionRef @Ticket
                  }
            }
    , contractDefinitions = deriveDefinitions @[Ticket, [Integer]]
    }

{- A top-level declaration splice that adds nothing. Its only job is to end the
declaration group above it: 'ualModule' reifies 'ticketSpend' to check its arity,
and GHC only puts a binding in the type environment once the group it belongs to
has been type-checked. Without this line the splice below fails with
"'ticketSpend' is not in the type environment at a reify". -}
$(pure [])

{- Below every ONCHAIN binding and past the group boundary above, which is what
'PlutusTx.Ual.TH.ualModule' requires. Further declarations may follow, as 'tests'
does; what may not is another annotated binding. -}
fixtureUal :: ModuleUal
fixtureUal = $(ualModule)

tests :: TestTree
tests =
  testGroup
    "TH"
    [ testCase "module name comes from the source header" $
        ualModuleName fixtureUal @?= UalModuleName "Ual.Fixture"
    , testCase "one ONCHAIN block, with its budget" $
        (onchainName <$> ualOnchain fixtureUal, onchainBudget <$> ualOnchain fixtureUal)
          @?= (["ticketSpend"], [Just (MkExecutionBudget 1883313 12342)])
    , testCase "the declared version survives" $
        (onchainVersion <$> ualOnchain fixtureUal) @?= [Just PlutusV3]
    , testCase "two resolved arguments, the second a list type" $
        (length . onchainResolvedArgs <$> ualOnchain fixtureUal) @?= [2]
    , testCase "one predicate, verbatim" $
        (Text.strip <$> ualPredicates fixtureUal)
          @?= ["def ticketOk (t : Integer) : Prop := t > 0"]
    , testCase "one property, with its natural-language text" $
        (propertyText <$> ualProperties fixtureUal)
          @?= ["A ticket with a positive value is accepted."]
    , testCase "one UPLC_DATA type" $
        ualUplcData fixtureUal @?= ["Ticket"]
    , testCase "ualIdFor agrees with the ONCHAIN name" $
        $(ualIdFor 'ticketSpend) @?= ("ticketSpend" :: Text.Text)
    ]

{- Manual negative checks.

The block openers below are written with a space after the brace-dash, because
'ualModule' reads this file as plain text: real openers here would be lexed as
further UAL blocks of this module and would fail the build on their own. Close
the gap when pasting an example in.

Each of these, pasted into this module above the `$(pure [])` line, must fail the
build with the message shown. All four were run against GHC 9.6.7 and the
messages are GHC's, wrapped here to the column limit.

  {- @ONCHAIN nosuch :: Integer -> () @-}
    -> ONCHAIN 'nosuch': no such value is in scope at the splice

  {- @ONCHAIN ticketSpend :: Integer -> () @-}
    -> ONCHAIN 'ticketSpend': signature declares 1 argument(s)
       but the Haskell type has 2

  {- @UPLC_DATA NoSuchType @-}
    -> ONCHAIN 'NoSuchType': no such type is in scope at the splice

  {- @ONCHAIN ticketSpend :: { (Ticket, Integer) : asData } -> Integer -> () @-}
    -> ONCHAIN '(Ticket, Integer)': only a plain type name or a list of one is
       supported in an ONCHAIN signature

The last two say "ONCHAIN" about a type name, because `renderUalError` prefixes
every `UnresolvedOnchainName` that way and the splice reuses that constructor for
type names too.

Re-run these by hand when changing `PlutusTx.Ual.TH`. A should-not-compile test
harness would be better; there is none in this package today. -}
