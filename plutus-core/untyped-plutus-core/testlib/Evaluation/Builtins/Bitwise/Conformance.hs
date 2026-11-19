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

import Evaluation.Builtins.Common (PlcTerm)
import Evaluation.Builtins.Conformance
  ( OutputFormat
  , PropertyId
  , TermCase (..)
  , generateTermFiles
  )
import Evaluation.Helpers (evaluateTheSame)
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)

import Data.ByteString (ByteString)
import Data.Maybe (mapMaybe)
import Hedgehog (Gen, Property, forAll, property)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Gen (evalGen)
import Hedgehog.Internal.Seed qualified as Seed
import Hedgehog.Internal.Tree (treeValue)
import Hedgehog.Range qualified as Range
import Test.QuickCheck qualified as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)

-- | Expected constants are used only by the normal tests, never emitted as inputs.
data Check
  = CheckSame PlcTerm PlcTerm
  | CheckConstant PlcTerm PlcTerm
  | CheckBoth Check Check
  deriving stock (Show)

checkSame :: PlcTerm -> PlcTerm -> Gen Check
checkSame lhs rhs = pure $ CheckSame lhs rhs

checkConstant :: forall a. PLC.Contains PLC.DefaultUni a => a -> PlcTerm -> Gen Check
checkConstant expected term = pure $ CheckConstant (mkConstant () expected) term

-- | Keep Hedgehog's input shrinking and normal assertion reporting.
checkProperty :: Gen Check -> Property
checkProperty gen = property $ forAll gen >>= check
  where
    check (CheckSame lhs rhs) = evaluateTheSame lhs rhs
    check (CheckConstant expected term) = evaluateTheSame expected term
    check (CheckBoth lhs rhs) = check lhs >> check rhs

genByteString :: Int -> Int -> Gen ByteString
genByteString lo hi = Gen.bytes $ Range.linear lo hi

genByteStringThat :: (ByteString -> Bool) -> Int -> Int -> Gen ByteString
genByteStringThat predicate lo hi = Gen.filter predicate $ genByteString lo hi

{-| Sample Hedgehog generators directly, with seeds derived from the executable's
QuickCheck seed. No property runner or assertions are involved. Discarded
inputs are retried, and the lazy stream stops at the requested case count.
Equality cases retain both terms, numbered together with -A/-B suffixes. -}
generateBitwisePropertyFiles
  :: OutputFormat -> FilePath -> Int -> QCGen -> PropertyId -> Gen Check -> IO ()
generateBitwisePropertyFiles format outputDir numFiles seed propertyId gen =
  generateTermFiles format outputDir numFiles propertyId $ concatMap terms cases
  where
    seeds = unGen (QC.infiniteListOf QC.arbitrary) seed 30
    cases = mapMaybe (\s -> treeValue <$> evalGen 30 (Seed.from s) gen) seeds
    terms (CheckSame lhs rhs) = [EqualTerms lhs rhs]
    terms (CheckConstant _ term) = [SingleTerm term]
    terms (CheckBoth lhs rhs) = terms lhs <> terms rhs
