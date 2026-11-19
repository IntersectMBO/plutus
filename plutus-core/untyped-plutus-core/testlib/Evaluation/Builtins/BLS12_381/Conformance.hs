{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Unevaluated BLS checks shared by normal tests and conformance generation.
module Evaluation.Builtins.BLS12_381.Conformance
  ( BlsCheck (..)
  , generateBlsPropertyFiles
  ) where

import Evaluation.Builtins.BLS12_381.Utils (compressionBit, isSet)
import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , bytestring
  , evalTerm
  , mkApp1
  )
import Evaluation.Builtins.Conformance
  ( OutputFormat
  , PropertyId
  , TermCase (..)
  , generateTermFiles
  )
import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn, mkTyBuiltinOf)
import UntypedPlutusCore qualified as UPLC

import Control.Lens (transformOf)
import Data.List (nub)
import Test.QuickCheck (Gen, Testable (property), infiniteListOf, (.&.), (===), (==>))
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)

{-| The Haskell-only checks are deliberately retained for normal test execution.
Export uses just their scripts; it never evaluates these assertions. -}
data BlsCheck
  = EvaluatesTo PlcTerm TypeErrorOrCekResult
  | SameResult PlcTerm PlcTerm
  | CompressionBitSet PlcTerm
  | DistinctResults [PlcTerm]
  | Given Bool BlsCheck

instance Testable BlsCheck where
  property (EvaluatesTo term expected) = evalTerm term === expected
  property (SameResult lhs rhs) = evalTerm lhs === evalTerm rhs
  property (CompressionBitSet term) = property $ case evalTerm term of
    CekSuccess (UPLC.Constant _ (PLC.Some (PLC.ValueOf PLC.DefaultUniByteString bs))) ->
      isSet compressionBit bs
    _ -> False
  property (DistinctResults terms) =
    let results = map evalTerm terms
     in property (all (/= CekError) results) .&. (length results === length (nub results))
  property (Given condition check) = condition ==> check

{-| The caller supplies the group's compressor for group-valued results.
Pairing tests return booleans and keep intermediate MlResult values inside
the program, so no non-serialisable value escapes into a fixture. -}
generateBlsPropertyFiles
  :: OutputFormat
  -> FilePath
  -> Int
  -> QCGen
  -> PropertyId
  -> (PlcTerm -> PlcTerm)
  -> Gen BlsCheck
  -> IO ()
generateBlsPropertyFiles format outputDir numCases seed propertyId compressResult gen =
  generateTermFiles format outputDir numCases propertyId $ concatMap terms cases
  where
    cases = unGen (infiniteListOf gen) seed 30
    groupResult = portableTerm . compressResult
    terms (EvaluatesTo term CekError) = [SingleTerm (groupResult term)]
    terms (EvaluatesTo term _) = [SingleTerm (portableTerm term)]
    terms (SameResult lhs rhs) = [EqualTerms (groupResult lhs) (groupResult rhs)]
    terms (CompressionBitSet term) = [SingleTerm (portableTerm term)]
    terms (DistinctResults ts) = map (SingleTerm . groupResult) ts
    terms (Given condition check) = if condition then terms check else []

{-| Group constants cannot be encoded in Flat. Reconstruct inputs from their
compressed bytes at runtime, including elements in multiScalarMul's lists.
This transformation runs only on exported scripts; normal properties retain
their original constant inputs. Budgets are measured after this transformation. -}
portableTerm :: PlcTerm -> PlcTerm
portableTerm = transformOf PLC.termSubterms replaceConstant
  where
    replaceConstant :: PlcTerm -> PlcTerm
    replaceConstant (PLC.Constant _ (PLC.Some (PLC.ValueOf PLC.DefaultUniBLS12_381_G1_Element p))) =
      g1Term p
    replaceConstant (PLC.Constant _ (PLC.Some (PLC.ValueOf PLC.DefaultUniBLS12_381_G2_Element p))) =
      g2Term p
    replaceConstant (PLC.Constant _ (PLC.Some (PLC.ValueOf (PLC.DefaultUniList PLC.DefaultUniBLS12_381_G1_Element) ps))) =
      pointList @G1.Element g1Term ps
    replaceConstant (PLC.Constant _ (PLC.Some (PLC.ValueOf (PLC.DefaultUniList PLC.DefaultUniBLS12_381_G2_Element) ps))) =
      pointList @G2.Element g2Term ps
    replaceConstant term = term
    g1Term = mkApp1 PLC.Bls12_381_G1_uncompress . bytestring . G1.compress
    g2Term = mkApp1 PLC.Bls12_381_G2_uncompress . bytestring . G2.compress

pointList :: forall g. PLC.DefaultUni `PLC.Contains` g => (g -> PlcTerm) -> [g] -> PlcTerm
pointList pointTerm = foldr cons (mkConstant () ([] @g))
  where
    cons point rest =
      mkIterAppNoAnn
        ( PLC.TyInst
            ()
            (builtin () PLC.MkCons)
            (mkTyBuiltinOf () (PLC.knownUni :: PLC.DefaultUni (PLC.Esc g)))
        )
        [pointTerm point, rest]
