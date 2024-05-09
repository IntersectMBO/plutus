-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.Laws (
  abelianSemigroupLaws,
  abelianMonoidLaws,
  idempotenceLaw,
  absorbtionLaw,
  leftDistributiveLaw,
  distributiveLaws,
  xorInvoluteLaw,
  complementSelfInverse,
  deMorgan,
  getSet,
  setGet,
  setSet,
  writeBitsHomomorphismLaws,
  replicateHomomorphismLaws,
  replicateIndex
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Common (typecheckEvaluateCek, typecheckReadKnownCek)
import GHC.Exts (fromString)
import Hedgehog (Gen, Property, PropertyT, annotateShow, failure, forAll, forAllWith, property,
                 (===))
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

replicateIndex :: TestTree
replicateIndex = testPropertyNamed "every byte is the same" "replicate_all_match" . property $ do
  n <- forAll . Gen.integral . Range.linear 1 $ 1024
  b <- forAll . Gen.integral . Range.constant 0 $ 255
  i <- forAll . Gen.integral . Range.linear 0 $ n - 1
  let lhsInner = mkIterAppNoAnn (builtin () PLC.ByteStringReplicate) [
        mkConstant @Integer () n,
        mkConstant @Integer () b
        ]
  let lhs = mkIterAppNoAnn (builtin () PLC.IndexByteString) [
        lhsInner,
        mkConstant @Integer () i
        ]
  let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsInteger) [
        lhs,
        mkConstant @Integer () b
        ]
  evaluateAndVerify (mkConstant @Bool () True) compareExp

getSet :: TestTree
getSet =
  testPropertyNamed "get-set" "get_set" . property $ do
    bs <- forAllByteString1
    i <- forAllIndexOf bs
    let lookupExp = mkIterAppNoAnn (builtin () PLC.ReadBit) [
          mkConstant @ByteString () bs,
          mkConstant @Integer () i
          ]
    case typecheckReadKnownCek def defaultBuiltinCostModel lookupExp of
      Left err -> annotateShow err >> failure
      Right (Left err) -> annotateShow err >> failure
      Right (Right b) -> do
        let lhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
              mkConstant @ByteString () bs,
              mkConstant @[(Integer, Bool)] () [(i, b)]
              ]
        let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
              lhs,
              mkConstant @ByteString () bs
              ]
        evaluateAndVerify (mkConstant @Bool () True) compareExp

setGet :: TestTree
setGet =
  testPropertyNamed "set-get" "set_get" . property $ do
    bs <- forAllByteString1
    i <- forAllIndexOf bs
    b <- forAll Gen.bool
    let lhsInner = mkIterAppNoAnn (builtin () PLC.WriteBits) [
          mkConstant @ByteString () bs,
          mkConstant @[(Integer, Bool)] () [(i, b)]
          ]
    let lhs = mkIterAppNoAnn (builtin () PLC.ReadBit) [
          lhsInner,
          mkConstant @Integer () i
          ]
    evaluateAndVerify (mkConstant @Bool () b) lhs

setSet :: TestTree
setSet =
  testPropertyNamed "set-set" "set_set" . property $ do
    bs <- forAllByteString1
    i <- forAllIndexOf bs
    b1 <- forAll Gen.bool
    b2 <- forAll Gen.bool
    let lhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
          mkConstant @ByteString () bs,
          mkConstant @[(Integer, Bool)] () [(i, b1), (i, b2)]
          ]
    let rhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
          mkConstant @ByteString () bs,
          mkConstant @[(Integer, Bool)] () [(i, b2)]
          ]
    let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
          lhs,
          rhs
          ]
    evaluateAndVerify (mkConstant @Bool () True) compareExp

writeBitsHomomorphismLaws :: TestTree
writeBitsHomomorphismLaws =
  testGroup "homomorphism to lists" [
    testPropertyNamed "identity -> []" "write_bits_h_1" identityProp,
    testPropertyNamed "composition -> concatenation" "write_bits_h_2" compositionProp
    ]
    where
      identityProp :: Property
      identityProp = property $ do
        bs <- forAllByteString1
        let lhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
              mkConstant @ByteString () bs,
              mkConstant @[(Integer, Bool)] () []
              ]
        let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
              lhs,
              mkConstant @ByteString () bs
              ]
        evaluateAndVerify (mkConstant @Bool () True) compareExp
      compositionProp :: Property
      compositionProp = property $ do
        bs <- forAllByteString1
        changelist1 <- forAllChangelistOf bs
        changelist2 <- forAllChangelistOf bs
        let lhsInner = mkIterAppNoAnn (builtin () PLC.WriteBits) [
              mkConstant @ByteString () bs,
              mkConstant @[(Integer, Bool)] () changelist1
              ]
        let lhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
              lhsInner,
              mkConstant @[(Integer, Bool)] () changelist2
              ]
        let rhs = mkIterAppNoAnn (builtin () PLC.WriteBits) [
              mkConstant @ByteString () bs,
              mkConstant @[(Integer, Bool)] () (changelist1 <> changelist2)
              ]
        let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
              lhs,
              rhs
              ]
        evaluateAndVerify (mkConstant @Bool () True) compareExp

replicateHomomorphismLaws :: TestTree
replicateHomomorphismLaws =
  testGroup "homomorphism" [
    testPropertyNamed "0 -> empty" "replicate_h_1" identityProp,
    testPropertyNamed "+ -> concat" "replicate_h_2" compositionProp
    ]
  where
    identityProp :: Property
    identityProp = property $ do
      b <- forAll . Gen.integral . Range.constant 0 $ 255
      let lhs = mkIterAppNoAnn (builtin () PLC.ByteStringReplicate) [
            mkConstant @Integer () 0,
            mkConstant @Integer () b
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            mkConstant @ByteString () ""
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp
    compositionProp :: Property
    compositionProp = property $ do
      b <- forAll . Gen.integral . Range.constant 0 $ 255
      n1 <- forAll . Gen.integral . Range.linear 0 $ 512
      n2 <- forAll . Gen.integral . Range.linear 0 $ 512
      let lhsInner1 = mkIterAppNoAnn (builtin () PLC.ByteStringReplicate) [
            mkConstant @Integer () n1,
            mkConstant @Integer () b
            ]
      let lhsInner2 = mkIterAppNoAnn (builtin () PLC.ByteStringReplicate) [
            mkConstant @Integer () n2,
            mkConstant @Integer () b
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.AppendByteString) [
            lhsInner1,
            lhsInner2
            ]
      let rhs = mkIterAppNoAnn (builtin () PLC.ByteStringReplicate) [
            mkConstant @Integer () (n1 + n2),
            mkConstant @Integer () b
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

complementSelfInverse :: TestTree
complementSelfInverse =
  testPropertyNamed "self-inverse" "self_inverse" . property $ do
    bs <- forAllByteString
    let lhsInner = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalComplement) [
          mkConstant @ByteString () bs
          ]
    let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalComplement) [
          lhsInner
          ]
    let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
          lhs,
          mkConstant @ByteString () bs
          ]
    evaluateAndVerify (mkConstant @Bool () True) compareExp

deMorgan :: TestTree
deMorgan = testGroup "De Morgan's laws" [
  testPropertyNamed "NOT AND -> OR" "demorgan_and" . go PLC.BitwiseLogicalAnd $ PLC.BitwiseLogicalOr,
  testPropertyNamed "NOT OR -> AND" "demorgan_or" . go PLC.BitwiseLogicalOr $ PLC.BitwiseLogicalAnd
  ]
  where
    go :: UPLC.DefaultFun -> UPLC.DefaultFun -> Property
    go f g = property $ do
      semantics <- forAllWith showSemantics Gen.bool
      bs1 <- forAllByteString
      bs2 <- forAllByteString
      let lhsInner = mkIterAppNoAnn (builtin () f) [
            mkConstant @Bool () semantics,
            mkConstant @ByteString () bs1,
            mkConstant @ByteString () bs2
            ]
      let lhs = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalComplement) [
            lhsInner
            ]
      let rhsInner1 = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalComplement) [
            mkConstant @ByteString () bs1
            ]
      let rhsInner2 = mkIterAppNoAnn (builtin () PLC.BitwiseLogicalComplement) [
            mkConstant @ByteString () bs2
            ]
      let rhs = mkIterAppNoAnn (builtin () g) [
            mkConstant @Bool () semantics,
            rhsInner1,
            rhsInner2
            ]
      let compareExp = mkIterAppNoAnn (builtin () PLC.EqualsByteString) [
            lhs,
            rhs
            ]
      evaluateAndVerify (mkConstant @Bool () True) compareExp

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

showSemantics :: Bool -> String
showSemantics b = if b
                      then "padding semantics"
                      else "truncation semantics"

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

forAllByteString1 :: PropertyT IO ByteString
forAllByteString1 = forAllWith hexShow . Gen.bytes . Range.linear 1 $ 1024

forAllIndexOf :: ByteString -> PropertyT IO Integer
forAllIndexOf bs = forAll . Gen.integral . Range.linear 0 . fromIntegral $ BS.length bs * 8 - 1

forAllChangelistOf :: ByteString -> PropertyT IO [(Integer, Bool)]
forAllChangelistOf bs =
  forAll . Gen.list (Range.linear 0 (8 * len - 1)) $ (,) <$> genIndex <*> Gen.bool
  where
    len :: Int
    len = BS.length bs
    genIndex :: Gen Integer
    genIndex = Gen.integral . Range.linear 0 . fromIntegral $ len * 8 - 1

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

