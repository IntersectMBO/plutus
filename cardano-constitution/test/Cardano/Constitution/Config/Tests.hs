{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{-| Test that the "examples"" inside the defaultConstitutionJSONSchema,
can be parsed with aeson. Usually the json-schema validators ignore these examples. -}
module Cardano.Constitution.Config.Tests
  ( tests
  ) where

import Cardano.Constitution.Config
import Cardano.Constitution.DataFilePaths as DFP

import Data.Aeson as Aeson
import Data.Aeson.THReader as Aeson
import Data.Aeson.Types as Aeson
import Data.Either
import Helpers.TestBuilders
import Test.Tasty.QuickCheck

defaultConstitutionJSONSchema :: Aeson.Value
defaultConstitutionJSONSchema =
  $$(Aeson.readJSONFromFile DFP.defaultConstitutionJSONSchemaFile)

{-| All the examples in the JSON schema are parseable as a list of ConstitutionConfigs.
Actually the examples 9005 and 9006 should not normally parse,
but currently they are not stopped by the Aeson instances. -}
examplesAsConfigsParser :: Value -> Aeson.Parser [ConstitutionConfig]
examplesAsConfigsParser = withObject "toplevel" (.: "examples")

-- all these are actually unit tests (by using QuickCheck.once)
test_parseSchemaExamples :: Property
test_parseSchemaExamples =
  once $
    let res = parseEither examplesAsConfigsParser defaultConstitutionJSONSchema
     in counterexample (fromLeft "cannot happen, must be left then" res) $
          isRight res

tests :: TestTreeWithTestState
tests =
  testGroup' "Config" $
    fmap
      (const . uncurry testProperty)
      [ ("parseSchemaExamples", test_parseSchemaExamples)
      ]
