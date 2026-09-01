{-# LANGUAGE OverloadedStrings #-}

module Ual.Assurance.Spec (tests) where

import Prelude

import Data.ByteString.Lazy qualified as LBS
import Data.List (intercalate)
import Data.Text (Text, unpack)
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
  , buildAssurance
  , encodeAssurance
  )
import PlutusTx.Blueprint.Write (encodeBlueprint)
import PlutusTx.Ual.Error (UalError (..), renderUalError)
import PlutusTx.Ual.Resolve (attachUal)
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  , emptyModuleUal
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)
import Test.Tasty.HUnit (testCase, (@?=))
import Ual.Fixture (fixtureContract, fixtureUal)

tests :: TestTree
tests =
  testGroup
    "Assurance"
    [ goldenVsText
        "document"
        "test/Ual/Golden/assurance.golden.json"
        (render (encodeAssurance doc))
    , buildTests
    , endToEndTests
    ]

{-| The whole pipeline over one annotated module: 'Ual.Fixture' carries the UAL,
@$(ualModule)@ has already extracted it into 'fixtureUal', and these two goldens
pin the documents an author would ship.

Both use 'error' on a 'Left'. That is the failure mode we want: a golden built
from an error message would compare equal to itself for ever, whereas an
exception fails the test with the rendered 'UalError'. -}
endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end to end"
    [ goldenVsText
        "blueprint"
        "test/Ual/Golden/end-to-end-plutus.golden.json"
        (render (encodeBlueprint (orDie (attachUal [fixtureUal] fixtureContract))))
    , goldenVsText
        "assurance"
        "test/Ual/Golden/end-to-end-assurance.golden.json"
        ( render
            ( encodeAssurance
                ( orDie
                    ( buildAssurance
                        (assurancePreamble doc)
                        (assuranceBlueprint doc)
                        "ticketSpend"
                        [fixtureUal]
                    )
                )
            )
        )
    ]

render :: LBS.ByteString -> Text
render = Text.decodeUtf8 . LBS.toStrict

{-| The value of a pipeline stage, or an exception carrying every error it
reported. -}
orDie :: Either [UalError] a -> a
orDie = either (error . intercalate "; " . map (unpack . renderUalError)) id

buildTests :: TestTree
buildTests =
  testGroup
    "buildAssurance"
    [ testCase "a module with no predicates produces no fragment" $
        (fmap fragmentId . assuranceFormalFragments)
          <$> build [modWith "A" [] [prop "p"]]
          @?= Right []
    , testCase "a property in a module with no fragment uses nothing" $
        (concatMap uses . assuranceProperties)
          <$> build [modWith "A" [] [prop "p"]]
          @?= Right []
    , testCase "a property in a module with a fragment uses that fragment" $
        (concatMap uses . assuranceProperties)
          <$> build [modWith "A" ["def a := 1"] [prop "p"]]
          @?= Right ["A"]
    , testCase "predicates are joined in source order, blank line separated" $
        (fmap fragmentSource . assuranceFormalFragments)
          <$> build [modWith "A" ["one", "two"] [prop "p"]]
          @?= Right ["one\n\ntwo"]
    , testCase "imports are restricted to modules that produced a fragment" $
        (fmap fragmentImports . assuranceFormalFragments)
          <$> build
            [ (modWith "A" ["a"] [prop "p"])
                { ualModuleImports = map UalModuleName ["B", "C", "Data.Text"]
                }
            , modWith "B" ["b"] []
            , modWith "C" [] []
            ]
          @?= Right [["B"], []]
    , testCase "no module declaring a property is rejected" $
        build [modWith "A" ["a"] []] @?= Left [NoProperties]
    , testCase "an empty module list is rejected" $
        build [] @?= Left [NoProperties]
    , testCase "duplicate property ids are reported" $
        build [modWith "A" [] [prop "p"], modWith "B" [] [prop "p"]]
          @?= Left [DuplicatePropertyId "p"]
    , testCase "a fragment import cycle is reported" $
        build
          [ (modWith "A" ["a"] [prop "p"]) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          ]
          @?= Left [FragmentCycle ["A", "B"]]
    , testCase "a fragment importing itself is a cycle" $
        build [(modWith "A" ["a"] [prop "p"]) {ualModuleImports = [UalModuleName "A"]}]
          @?= Left [FragmentCycle ["A"]]
    , testCase "two disjoint cycles report the first one found" $
        build
          [ (modWith "A" ["a"] [prop "p"]) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          , (modWith "C" ["c"] []) {ualModuleImports = [UalModuleName "D"]}
          , (modWith "D" ["d"] []) {ualModuleImports = [UalModuleName "C"]}
          ]
          @?= Left [FragmentCycle ["A", "B"]]
    , testCase "a diamond of imports is not a cycle" $
        (fmap fragmentImports . assuranceFormalFragments)
          <$> build
            [ (modWith "A" ["a"] [prop "p"]) {ualModuleImports = map UalModuleName ["B", "C"]}
            , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "D"]}
            , (modWith "C" ["c"] []) {ualModuleImports = [UalModuleName "D"]}
            , modWith "D" ["d"] []
            ]
          @?= Right [["B", "C"], ["D"], ["D"], []]
    , testCase "errors of both kinds are collected" $
        build
          [ (modWith "A" ["a"] [prop "p"]) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] [prop "p"]) {ualModuleImports = [UalModuleName "A"]}
          ]
          @?= Left [DuplicatePropertyId "p", FragmentCycle ["A", "B"]]
    , testCase "a missing property list does not hide a cycle" $
        build
          [ (modWith "A" ["a"] []) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          ]
          @?= Left [FragmentCycle ["A", "B"], NoProperties]
    ]
  where
    build = buildAssurance (assurancePreamble doc) (assuranceBlueprint doc) "ticket-spend"
    uses p = maybe [] formalUses (statementFormal (propertyStatement p))
    modWith n preds props =
      (emptyModuleUal (UalModuleName n))
        { ualPredicates = preds
        , ualProperties = props
        }
    prop n =
      MkPropertyDecl
        { propertyName = n
        , propertyText = "t"
        , propertyBody = "True"
        , propertyLine = 1
        }

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
