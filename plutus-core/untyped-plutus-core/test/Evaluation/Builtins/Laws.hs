{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.Laws (
  abelianSemigroupLaws,
  abelianMonoidLaws,
  idempotenceLaw,
  absorbtionLaw,
  leftDistributiveLaw,
  distributiveLaws,
  xorInvoluteLaw
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Common (typecheckEvaluateCek)
import GHC.Exts (fromString)
import Hedgehog (Property, PropertyT, annotateShow, failure, forAllWith, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric (showHex)
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultBuiltinCostModel)
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusPrelude (Word8, def)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)
import UntypedPlutusCore qualified as UPLC

xorInvoluteLaw :: TestTree
xorInvoluteLaw = testPropertyNamed "involute (both)" "involute_both" . property $ do
  bs <- forAllByteString
  semantics <- forAllWith showSemantics Gen.bool
  let lhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalXor) [
        mkConstant @Bool () semantics,
        mkConstant @ByteString () bs,
        mkConstant @ByteString () bs
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalXor) [
        mkConstant @Bool () semantics,
        mkConstant @ByteString () bs,
        lhsInner
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        mkConstant @ByteString () bs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp
  where
    showSemantics :: Bool -> String
    showSemantics b = if b
                      then "padding semantics"
                      else "truncation semantics"

leftDistributiveLaw :: String -> String -> UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> TestTree
leftDistributiveLaw name distOpName f distOp isPadding =
  testPropertyNamed ("left distribution (" <> name <> ") over " <> distOpName)
                    ("left_distribution_" <> fromString name <> "_" <> fromString distOpName)
                    (leftDistProp f distOp isPadding)

distributiveLaws :: String -> UPLC.DefaultFun -> Bool -> TestTree
distributiveLaws name f isPadding =
  testGroup ("distributivity over itself (" <> name <> ")") [
    testPropertyNamed "left distribution" "left_distribution" (leftDistProp f f isPadding),
    testPropertyNamed "right distribution" "right_distribution" (rightDistProp f isPadding)
    ]

abelianSemigroupLaws :: String -> UPLC.DefaultFun -> Bool -> TestTree
abelianSemigroupLaws name f isPadding =
  testGroup ("abelian semigroup (" <> name <> ")") [
    testPropertyNamed "commutativity" "commutativity" (commProp f isPadding),
    testPropertyNamed "associativity" "associativity" (assocProp f isPadding)
    ]

abelianMonoidLaws :: String -> UPLC.DefaultFun -> Bool -> ByteString -> TestTree
abelianMonoidLaws name f isPadding unit =
  testGroup ("abelian monoid (" <> name <> ")") [
    testPropertyNamed "commutativity" "commutativity" (commProp f isPadding),
    testPropertyNamed "associativity" "associativity" (assocProp f isPadding),
    testPropertyNamed "unit" "unit" (unitProp f isPadding unit)
    ]

idempotenceLaw :: String -> UPLC.DefaultFun -> Bool -> TestTree
idempotenceLaw name f isPadding =
  testPropertyNamed ("idempotence (" <> name <> ")")
                    ("idempotence_" <> fromString name)
                    idempProp
  where
    idempProp :: Property
    idempProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () f) [
            mkConstant @Bool () isPadding,
            mkConstant @ByteString () bs,
            mkConstant @ByteString () bs
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            mkConstant @ByteString () bs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

absorbtionLaw :: String -> UPLC.DefaultFun -> Bool -> ByteString -> TestTree
absorbtionLaw name f isPadding absorber =
  testPropertyNamed ("absorbing element (" <> name <> ")")
                    ("absorbing_element_" <> fromString name)
                    absorbProp
  where
    absorbProp :: Property
    absorbProp = property $ do
      bs <- forAllByteString
      let lhs = mkIterAppNoAnn (builtin () f) [
            mkConstant @Bool () isPadding,
            mkConstant @ByteString () bs,
            mkConstant @ByteString () absorber
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            mkConstant @ByteString () absorber,
            lhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

-- Helpers

leftDistProp :: UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> Property
leftDistProp f distOp isPadding = property $ do
  x <- forAllByteString
  y <- forAllByteString
  z <- forAllByteString
  let distLhs = mkIterAppNoAnn (builtin () distOp) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () y,
        mkConstant @ByteString () z
        ]
  let lhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () x,
        distLhs
        ]
  let distRhs1 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () x,
        mkConstant @ByteString () y
        ]
  let distRhs2 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () x,
        mkConstant @ByteString () z
        ]
  let rhs = mkIterAppNoAnn (builtin () distOp) [
        mkConstant @Bool () isPadding,
        distRhs1,
        distRhs2
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

rightDistProp :: UPLC.DefaultFun -> Bool -> Property
rightDistProp f isPadding = property $ do
  x <- forAllByteString
  y <- forAllByteString
  z <- forAllByteString
  let lhsInner = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () x,
        mkConstant @ByteString () y
        ]
  let lhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        lhsInner,
        mkConstant @ByteString () z
        ]
  let rhsInner1 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () x,
        mkConstant @ByteString () z
        ]
  let rhsInner2 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () y,
        mkConstant @ByteString () z
        ]
  let rhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        rhsInner1,
        rhsInner2
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

commProp :: UPLC.DefaultFun -> Bool -> Property
commProp f isPadding = property $ do
  data1 <- forAllByteString
  data2 <- forAllByteString
  let lhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () data1,
        mkConstant @ByteString () data2
        ]
  let rhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () data2,
        mkConstant @ByteString () data1
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

assocProp :: UPLC.DefaultFun -> Bool -> Property
assocProp f isPadding = property $ do
  data1 <- forAllByteString
  data2 <- forAllByteString
  data3 <- forAllByteString
  let data12 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () data1,
        mkConstant @ByteString () data2
        ]
  let lhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        data12,
        mkConstant @ByteString () data3
        ]
  let data23 = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () data2,
        mkConstant @ByteString () data3
        ]
  let rhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () data1,
        data23
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        rhs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

unitProp :: UPLC.DefaultFun -> Bool -> ByteString -> Property
unitProp f isPadding unit = property $ do
  bs <- forAllByteString
  let lhs = mkIterAppNoAnn (builtin () f) [
        mkConstant @Bool () isPadding,
        mkConstant @ByteString () bs,
        mkConstant @ByteString () unit
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
        lhs,
        mkConstant @ByteString () bs
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

forAllByteString :: PropertyT IO ByteString
forAllByteString = forAllWith hexShow . Gen.bytes . Range.linear 0 $ 1024

hexShow :: ByteString -> String
hexShow = ("0x" <>) . BS.foldl' (\acc w8 -> acc <> byteToHex w8) ""
  where
    byteToHex :: Word8 -> String
    byteToHex w8
      | w8 < 128 = "0" <> showHex w8 ""
      | otherwise = showHex w8 ""

evaluateAndVerify ::
  UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PLC.Term UPLC.TyName UPLC.Name UPLC.DefaultUni UPLC.DefaultFun () ->
  PropertyT IO ()
evaluateAndVerify expected actual =
  case typecheckEvaluateCek def defaultBuiltinCostModel actual of
    Left x -> annotateShow x >> failure
    Right (res, logs) -> case res of
      PLC.EvaluationFailure   -> annotateShow logs >> failure
      PLC.EvaluationSuccess r -> r === expected

