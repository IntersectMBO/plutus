{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Unevaluated BLS checks shared by normal tests and conformance generation.
module Evaluation.Builtins.BLS12_381.Conformance
  ( generateBlsPropertyFiles
  , hasCompressionBit
  ) where

import Evaluation.Builtins.BLS12_381.Utils (compressionBit, isSet)
import Evaluation.Builtins.Common
  ( PlcTerm
  , TypeErrorOrCekResult (..)
  , bytestring
  , mkApp1
  )
import Evaluation.Builtins.Conformance
  ( Check (..)
  , CheckMode
  , Generated
  , OutputFormat
  , PropertyId
  , TermCase (..)
  , caseTermsUnchecked
  , generateTermFiles
  , guardCheck
  , propertySeed
  , samplingSize
  )
import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as G2
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn, mkTyBuiltinOf)
import UntypedPlutusCore qualified as UPLC

import Control.Lens (transformOf)
import Test.QuickCheck (Gen, infiniteListOf)
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)

-- | The evaluated term returned a bytestring with the compression bit set.
hasCompressionBit :: TypeErrorOrCekResult -> Bool
hasCompressionBit
  (CekSuccess (UPLC.Constant _ (PLC.Some (PLC.ValueOf PLC.DefaultUniByteString bs)))) =
    isSet compressionBit bs
hasCompressionBit _ = False

{-| The caller supplies the group's compressor for group-valued results.
Pairing tests return booleans and keep intermediate MlResult values inside
the program, so no non-serialisable value escapes into a generated test case. -}
generateBlsPropertyFiles
  :: OutputFormat
  -> CheckMode
  -> FilePath
  -> Int
  -> QCGen
  -> PropertyId
  -> String
  -> (PlcTerm -> PlcTerm)
  -> Gen Check
  -> IO Generated
generateBlsPropertyFiles format mode outputDir numCases seed propertyId description compressResult gen =
  generateTermFiles format outputDir numCases propertyId description $
    concatMap termCases cases
  where
    cases = unGen (infiniteListOf gen) (propertySeed seed propertyId) samplingSize
    groupResult = portableTerm . compressResult
    -- The property is checked on the original check, as the normal tests do,
    -- and only then are the terms rewritten for export.
    termCases check = guardCheck mode check (portableTermCases check)
    -- Group-valued results are compressed so that the exported programs and
    -- their expected results can be encoded.
    portableTermCases check = case check of
      CheckEq lhs rhs -> [EqualTerms (groupResult lhs) (groupResult rhs)]
      CheckEvaluatesTo term CekError -> [SingleTerm (groupResult term)]
      CheckEvaluatesTo term _ -> [SingleTerm (portableTerm term)]
      CheckSatisfies _ term _ -> [SingleTerm (portableTerm term)]
      CheckDistinct terms -> map (SingleTerm . groupResult) terms
      CheckBoth a b -> portableTermCases a <> portableTermCases b
      CheckImplies condition inner -> if condition then portableTermCases inner else []
      _ -> caseTermsUnchecked check

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
