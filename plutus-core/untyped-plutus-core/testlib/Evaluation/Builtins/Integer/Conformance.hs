{-# LANGUAGE FlexibleInstances #-}

{-| Assertions and specifications shared by normal integer properties and
conformance generators. -}
module Evaluation.Builtins.Integer.Conformance
  ( Check (..)
  , PropertyReport (..)
  , PropertySpec (..)
  , generatePropertySpecs
  , propertySpec
  , propertySpecPropertyIds
  , testPropertySpecs
  ) where

import Evaluation.Builtins.Conformance
  ( Check (..)
  , CheckMode
  , Generated
  , OutputFormat
  , PropertyFilter
  , PropertyId (..)
  , PropertyReport (..)
  , PropertySpec (..)
  , caseTerms
  , checkUniqueIds
  , generateTermFiles
  , propertySeed
  , propertySpecPropertyIds
  , samplingSize
  )

import Control.Monad (forM)
import Data.Maybe (catMaybes)
import Test.QuickCheck
  ( Arbitrary (arbitrary)
  , Gen
  , Property
  , Testable (property)
  , infiniteListOf
  )
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.QuickCheck (testProperty)

{-| Sample the inputs of a property without invoking QuickCheck's test runner.
This is the bridge from QuickCheck-style properties to 'PropertySpec'. -}
class GenerateCases prop where
  caseGenerator :: prop -> Gen Check

instance GenerateCases Check where
  caseGenerator = pure

instance GenerateCases prop => GenerateCases (Gen prop) where
  caseGenerator gen = gen >>= caseGenerator

instance (Arbitrary a, GenerateCases prop) => GenerateCases (a -> prop) where
  caseGenerator f = arbitrary >>= caseGenerator . f

{-| A property described once and used by both the test suite and the
conformance test generator. The identifier is the stable test case name; the
description is what the test runner displays. -}
propertySpec :: GenerateCases prop => String -> TestName -> prop -> PropertySpec (Gen Check)
propertySpec identifier description prop =
  PropertySpec identifier description (caseGenerator prop)

-- | Tasty tests for a group of properties, applying a limit to each.
testPropertySpecs
  :: (Property -> Property) -> [PropertySpec (Gen Check)] -> [TestTree]
testPropertySpecs adjust =
  map $ \spec ->
    testProperty (propertySpecDescription spec) $
      adjust (property (propertySpecCheck spec))

{-| Export exactly the requested number of cases without running the property
assertions. Terms are sampled lazily using QuickCheck's generators; sampling
stops as soon as the quota is reached. Equality cases emit both terms with a
shared number and -A/-B suffixes. Each exported term is evaluated once to
obtain its expected result and budget. Files from a previous run with the same
names are overwritten; other files are left untouched.

Numbers are padded to five digits. Output is placed in:
<property-id-path>/<property-id-name>-<n>[-A|-B]/<property-id-name>-<n>[-A|-B]
with .uplc and/or .flat inputs, matching .expected files, and .budget.expected. -}
generatePropertyFiles
  :: OutputFormat
  -> CheckMode
  -> FilePath
  -> Int
  -> QCGen
  -> PropertyId
  -> String
  -> Gen Check
  -> IO Generated
generatePropertyFiles format mode outputDir numFiles seed propertyId description gen =
  generateTermFiles format outputDir numFiles propertyId description terms
  where
    -- Match the size used by QuickCheck's 'generate', with an explicit seed.
    cases = unGen (infiniteListOf gen) (propertySeed seed propertyId) samplingSize
    terms = concatMap (caseTerms mode) cases

{-| Generate the requested number of cases for every selected property,
writing them below the suite directory. -}
generatePropertySpecs
  :: OutputFormat
  -> CheckMode
  -> PropertyFilter
  -> FilePath
  -> Int
  -> QCGen
  -> [String]
  -> [PropertySpec (Gen Check)]
  -> IO [PropertyReport]
generatePropertySpecs format mode include outputDir numFiles seed suiteDirectory specs = do
  checkUniqueIds suiteDirectory specs
  catMaybes
    <$> forM
      specs
      ( \spec -> do
          let propertyId = PropertyId suiteDirectory (propertySpecId spec)
          if include propertyId
            then
              Just . PropertyReport propertyId
                <$> generatePropertyFiles
                  format
                  mode
                  outputDir
                  numFiles
                  seed
                  propertyId
                  (propertySpecDescription spec)
                  (propertySpecCheck spec)
            else pure Nothing
      )
