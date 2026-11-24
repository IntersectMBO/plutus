{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

-- | Share Hedgehog inputs and terms between assertions and conformance generation.
module Evaluation.Builtins.Bitwise.Conformance
  ( Check (..)
  , checkSame
  , checkConstant
  , checkProperty
  , genByteString
  , genByteStringThat
  , generateBitwisePropertyFiles
  ) where

import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , cekSuccessTrue
  , evalTerm
  )
import Evaluation.Builtins.Conformance
  ( Check (..)
  , CheckMode
  , Generated
  , OutputFormat
  , PropertyId
  , caseTerms
  , generateTermFiles
  , isCekSuccess
  , propertySeed
  , samplingSize
  )
import Evaluation.Helpers (evaluateTheSame)
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)

import Data.ByteString (ByteString)
import Data.List (nub)
import Data.Maybe (mapMaybe)
import Hedgehog
  ( Gen
  , Property
  , annotate
  , annotateShow
  , assert
  , failure
  , forAll
  , property
  , success
  , (===)
  )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Gen (evalGen)
import Hedgehog.Internal.Seed qualified as Seed
import Hedgehog.Internal.Tree (treeValue)
import Hedgehog.Range qualified as Range
import Test.QuickCheck qualified as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)

checkSame :: PlcTerm -> PlcTerm -> Gen Check
checkSame lhs rhs = pure $ CheckEq lhs rhs

{-| Compare a term's result with a constant. The constant is only used by the
normal tests; the generated tests export the term alone. -}
checkConstant :: forall a. PLC.Contains PLC.DefaultUni a => a -> PlcTerm -> Gen Check
checkConstant expected term =
  pure $ CheckEvaluatesTo term (CekSuccess (mkConstant () expected))

-- | Keep Hedgehog's input shrinking and normal assertion reporting.
checkProperty :: Gen Check -> Property
checkProperty gen = property $ forAll gen >>= check
  where
    check (CheckEq lhs rhs) = evaluateTheSame lhs rhs
    check (CheckEvaluatesTo term expected) = evalTerm term === expected
    check (CheckTrue term) = evalTerm term === cekSuccessTrue
    check (CheckOk term) = case evalTerm term of
      CekSuccess _ -> success
      result -> annotateShow result >> failure
    check (CheckFails term) = evalTerm term === CekError
    check (CheckBoth lhs rhs) = check lhs >> check rhs
    check (CheckImplies condition inner) = if condition then check inner else success
    check (CheckDistinct terms) =
      let results = map evalTerm terms
       in assert (all isCekSuccess results && length results == length (nub results))
    check (CheckSatisfies label term predicate) =
      annotate label >> assert (predicate (evalTerm term))

genByteString :: Int -> Int -> Gen ByteString
genByteString lo hi = Gen.bytes $ Range.linear lo hi

genByteStringThat :: (ByteString -> Bool) -> Int -> Int -> Gen ByteString
genByteStringThat predicate lo hi = Gen.filter predicate $ genByteString lo hi

{-| Sample Hedgehog generators directly, with seeds derived from the executable's
QuickCheck seed. No property runner or assertions are involved. Discarded
inputs are retried, and the lazy stream stops at the requested case count.
Equality cases retain both terms, numbered together with -A/-B suffixes. -}
generateBitwisePropertyFiles
  :: OutputFormat
  -> CheckMode
  -> FilePath
  -> Int
  -> QCGen
  -> PropertyId
  -> String
  -> Gen Check
  -> IO Generated
generateBitwisePropertyFiles format mode outputDir numFiles seed propertyId description gen =
  generateTermFiles format outputDir numFiles propertyId description $
    concatMap (caseTerms mode) cases
  where
    seeds = unGen (QC.infiniteListOf QC.arbitrary) (propertySeed seed propertyId) samplingSize
    cases = mapMaybe (\s -> treeValue <$> evalGen (Range.Size samplingSize) (Seed.from s) gen) seeds
