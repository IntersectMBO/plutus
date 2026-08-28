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
  , buildAssurance
  , encodeAssurance
  )
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , PropertyDecl (..)
  , UalModuleName (..)
  , emptyModuleUal
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Extras (goldenVsText)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests =
  testGroup
    "Assurance"
    [ goldenVsText
        "document"
        "test/Ual/Golden/assurance.golden.json"
        (Text.decodeUtf8 (LBS.toStrict (encodeAssurance doc)))
    , buildTests
    ]

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
          <$> build [modWith "A" ["one", "two"] []]
          @?= Right ["one\n\ntwo"]
    , testCase "imports are restricted to modules that produced a fragment" $
        (fmap fragmentImports . assuranceFormalFragments)
          <$> build
            [ (modWith "A" ["a"] []) {ualModuleImports = map UalModuleName ["B", "C", "Data.Text"]}
            , modWith "B" ["b"] []
            , modWith "C" [] []
            ]
          @?= Right [["B"], []]
    , testCase "duplicate property ids are reported" $
        build [modWith "A" [] [prop "p"], modWith "B" [] [prop "p"]]
          @?= Left [DuplicatePropertyId "p"]
    , testCase "a fragment import cycle is reported" $
        build
          [ (modWith "A" ["a"] []) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          ]
          @?= Left [FragmentCycle ["A", "B"]]
    , testCase "a fragment importing itself is a cycle" $
        build [(modWith "A" ["a"] []) {ualModuleImports = [UalModuleName "A"]}]
          @?= Left [FragmentCycle ["A"]]
    , testCase "two disjoint cycles report the first one found" $
        build
          [ (modWith "A" ["a"] []) {ualModuleImports = [UalModuleName "B"]}
          , (modWith "B" ["b"] []) {ualModuleImports = [UalModuleName "A"]}
          , (modWith "C" ["c"] []) {ualModuleImports = [UalModuleName "D"]}
          , (modWith "D" ["d"] []) {ualModuleImports = [UalModuleName "C"]}
          ]
          @?= Left [FragmentCycle ["A", "B"]]
    , testCase "a diamond of imports is not a cycle" $
        (fmap fragmentImports . assuranceFormalFragments)
          <$> build
            [ (modWith "A" ["a"] []) {ualModuleImports = map UalModuleName ["B", "C"]}
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
