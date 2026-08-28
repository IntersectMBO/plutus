{-# LANGUAGE OverloadedStrings #-}

module Ual.Assurance.Spec (tests) where

import Prelude

import Data.ByteString.Lazy qualified as LBS
import Data.Text.Encoding qualified as Text
import PlutusTx.Assurance
  ( AssuranceDocument (..)
  , AssurancePreamble (..)
  , BlueprintRef (..)
  , Digest (..)
  , FormalFragment (..)
  , FormalStatement (..)
  , Property (..)
  , RegistryEntry (..)
  , Statement (..)
  , encodeAssurance
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)

tests :: TestTree
tests =
  testGroup
    "Assurance"
    [ goldenVsText
        "document"
        "test/Ual/Golden/assurance.golden.json"
        (Text.decodeUtf8 (LBS.toStrict (encodeAssurance doc)))
    ]

doc :: AssuranceDocument
doc =
  MkAssuranceDocument
    { assurancePreamble =
        MkAssurancePreamble
          { assuranceTitle = "Ticket contract — UAL assurance"
          , assuranceDescription = Just "Generated from UAL annotations."
          , assuranceVersion = Just "1.0.0"
          , assuranceAuthors = ["Example Author <a@example.com>"]
          , assuranceCreated = "2026-08-24"
          , assuranceLicense = Just "CC-BY-4.0"
          }
    , assuranceBlueprint =
        MkBlueprintRef
          { blueprintUri = "plutus.json"
          , blueprintHash = Just (MkDigest "sha256" "0f")
          }
    , assuranceLanguages =
        [
          ( "ual"
          , MkRegistryEntry
              { registryName = "Universal Annotation Language"
              , registryVersion = "0.4"
              , registryUri = Just "https://github.com/input-output-hk/ual-spec"
              , registryDescription = Nothing
              }
          )
        ]
    , assuranceTools = []
    , assuranceFormalFragments =
        [ MkFormalFragment
            { fragmentId = "My.Contract"
            , fragmentLanguage = "ual"
            , fragmentImports = ["My.Types"]
            , fragmentSource = "def ok : Prop := True"
            }
        ]
    , assuranceProperties =
        [ MkProperty
            { propertyIdent = "ticket_ok"
            , propertyTitle = Nothing
            , propertyValidators = ["ticket-spend"]
            , propertyStatement =
                MkStatement
                  { statementText = "A valid ticket is always accepted."
                  , statementFormal =
                      Just
                        MkFormalStatement
                          { formalLanguage = "ual"
                          , formalUses = ["My.Contract"]
                          , formalSource = "\8704 t, ok t"
                          }
                  }
            }
        ]
    }
