-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{-| Tests for [CIP-0122](https://cips.cardano.org/cip/CIP-0122) (the first
batch of bitwise builtins) -}
module Evaluation.Builtins.Bitwise.CIP0122
  ( abelianSemigroupLaws
  , abelianMonoidLaws
  , idempotenceLaw
  , absorbtionLaw
  , leftDistributiveLaw
  , distributiveLaws
  , xorInvoluteLaw
  , complementSelfInverse
  , deMorgan
  , getSet
  , setGet
  , setSet
  , writeBitsHomomorphismLaws
  , replicateHomomorphismLaws
  , replicateIndex
  , generate_bitwise_cip0122_properties
  ) where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusCore.Test (mapTestLimitAtLeast)
import UntypedPlutusCore qualified as UPLC

import Data.Bits qualified as Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Builtins.Bitwise.Conformance
import Evaluation.Builtins.Conformance (OutputFormat)
import GHC.Exts (fromString)
import Hedgehog (Gen, Property)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import System.FilePath ((</>))
import Test.QuickCheck.Random (QCGen)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)

{-| Any call to 'replicateByteString' must produce the same byte at
every valid index, namely the byte specified. -}
replicateIndex :: TestTree
replicateIndex =
  testPropertyNamed "every byte is the same" "replicate_all_match" $
    mapTestLimitAtLeast 99 (`div` 20) $
      checkProperty replicateIndexCases

{-| If you retrieve a bit value at an index, then write that same value to
the same index, nothing should happen. -}
getSet :: TestTree
getSet =
  testPropertyNamed "get-set" "get_set" . mapTestLimitAtLeast 50 (`div` 20) $
    checkProperty getSetCases

{-| If you write a bit value to an index, then retrieve the bit value at the
same index, you should get back what you wrote. -}
setGet :: TestTree
setGet =
  testPropertyNamed "set-get" "set_get" . mapTestLimitAtLeast 99 (`div` 10) $
    checkProperty setGetCases

-- | If you write twice to the same bit index, the second write should win.
setSet :: TestTree
setSet =
  testPropertyNamed "set-set" "set_set" . mapTestLimitAtLeast 50 (`div` 20) $
    checkProperty setSetCases

{-| Checks that:

* Writing with an empty list of positions does nothing; and if you write a
* boolean b with one list of positions, then a second, it is the same as
* writing b with their concatenation. -}
writeBitsHomomorphismLaws :: TestTree
writeBitsHomomorphismLaws =
  testGroup
    "homomorphism to lists"
    [ testPropertyNamed "identity -> []" "write_bits_h_1_false" $
        mapTestLimitAtLeast 99 (`div` 20) (identityProp False)
    , testPropertyNamed "identity -> []" "write_bits_h_1_true" $
        mapTestLimitAtLeast 99 (`div` 20) (identityProp True)
    , testPropertyNamed "composition -> concatenation" "write_bits_h_2_false" $
        mapTestLimitAtLeast 50 (`div` 20) (compositionProp False)
    , testPropertyNamed "composition -> concatenation" "write_bits_h_2_true" $
        mapTestLimitAtLeast 50 (`div` 20) (compositionProp True)
    ]
  where
    identityProp :: Bool -> Property
    identityProp b = checkProperty (writeBitsIdentityCases b)
    compositionProp :: Bool -> Property
    compositionProp b = checkProperty (writeBitsCompositionCases b)

{-| Checks that:

* Replicating any byte 0 times produces the empty 'ByteString'; and
* Replicating a byte @n@ times, then replicating a byte @m@ times and
  concatenating the results, is the same as replicating that byte @n + m@
  times. -}
replicateHomomorphismLaws :: TestTree
replicateHomomorphismLaws =
  testGroup
    "homomorphism"
    [ testPropertyNamed "0 -> empty" "replicate_h_1" $
        mapTestLimitAtLeast 99 (`div` 20) identityProp
    , testPropertyNamed "+ -> concat" "replicate_h_2" $
        mapTestLimitAtLeast 50 (`div` 20) compositionProp
    ]
  where
    identityProp :: Property
    identityProp = checkProperty replicateIdentityCases
    compositionProp :: Property
    compositionProp = checkProperty replicateCompositionCases

-- | If you complement a 'ByteString' twice, nothing should change.
complementSelfInverse :: TestTree
complementSelfInverse =
  testPropertyNamed "self-inverse" "self_inverse" $
    mapTestLimitAtLeast 99 (`div` 20) $
      checkProperty complementSelfInverseCases

{-| Checks that:

* The complement of an AND is an OR of complements; and
* The complement of an OR is an AND of complements. -}
deMorgan :: TestTree
deMorgan =
  testGroup
    "De Morgan's laws"
    [ testPropertyNamed "NOT AND -> OR" "demorgan_and" . go PLC.AndByteString $ PLC.OrByteString
    , testPropertyNamed "NOT OR -> AND" "demorgan_or" . go PLC.OrByteString $ PLC.AndByteString
    ]
  where
    go :: UPLC.DefaultFun -> UPLC.DefaultFun -> Property
    go f g = mapTestLimitAtLeast 50 (`div` 10) $ checkProperty (deMorganCases f g)

-- | If you XOR any 'ByteString' with itself twice, nothing should change.
xorInvoluteLaw :: TestTree
xorInvoluteLaw =
  testPropertyNamed "involute (both)" "involute_both" $
    mapTestLimitAtLeast 99 (`div` 20) $
      checkProperty xorInvoluteLawCases

{-| Checks that the first 'DefaultFun' distributes over the second from the
left, given the specified semantics (as a 'Bool'). More precisely, for
'DefaultFun's @f@ and @g@, checks that @f x (g y z) = g (f x y) (f x z)@. -}
leftDistributiveLaw :: String -> String -> UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> TestTree
leftDistributiveLaw name distOpName f distOp isPadding =
  testPropertyNamed
    ("left distribution (" <> name <> ") over " <> distOpName)
    ("left_distribution_" <> fromString name <> "_" <> fromString distOpName)
    (mapTestLimitAtLeast 50 (`div` 10) $ leftDistProp f distOp isPadding)

-- | Checks that the given function self-distributes both left and right.
distributiveLaws :: String -> UPLC.DefaultFun -> Bool -> TestTree
distributiveLaws name f isPadding =
  testGroup
    ("distributivity over itself (" <> name <> ")")
    [ testPropertyNamed "left distribution" "left_distribution" $
        mapTestLimitAtLeast 50 (`div` 10) $
          leftDistProp f f isPadding
    , testPropertyNamed "right distribution" "right_distribution" $
        mapTestLimitAtLeast 50 (`div` 10) $
          rightDistProp f isPadding
    ]

{-| Checks that the given 'DefaultFun', under the given semantics, forms an
abelian semigroup: that is, the operation both commutes and associates. -}
abelianSemigroupLaws :: String -> UPLC.DefaultFun -> Bool -> TestTree
abelianSemigroupLaws name f isPadding =
  testGroup
    ("abelian semigroup (" <> name <> ")")
    [ testPropertyNamed "commutativity" "commutativity" $
        mapTestLimitAtLeast 50 (`div` 10) $
          commProp f isPadding
    , testPropertyNamed "associativity" "associativity" $
        mapTestLimitAtLeast 50 (`div` 10) $
          assocProp f isPadding
    ]

{-| As 'abelianSemigroupLaws', but also checks that the provided 'ByteString'
is both a left and right identity. -}
abelianMonoidLaws :: String -> UPLC.DefaultFun -> Bool -> ByteString -> TestTree
abelianMonoidLaws name f isPadding unit =
  testGroup
    ("abelian monoid (" <> name <> ")")
    [ testPropertyNamed "commutativity" "commutativity" $
        mapTestLimitAtLeast 50 (`div` 10) $
          commProp f isPadding
    , testPropertyNamed "associativity" "associativity" $
        mapTestLimitAtLeast 50 (`div` 10) $
          assocProp f isPadding
    , testPropertyNamed "unit" "unit" $
        mapTestLimitAtLeast 75 (`div` 15) $
          unitProp f isPadding unit
    ]

{-| Checks that the provided 'DefaultFun', under the given semantics, is
idempotent; namely, that @f x x = x@ for any @x@. -}
idempotenceLaw :: String -> UPLC.DefaultFun -> Bool -> TestTree
idempotenceLaw name f isPadding =
  testPropertyNamed
    ("idempotence (" <> name <> ")")
    ("idempotence_" <> fromString name)
    (mapTestLimitAtLeast 75 (`div` 15) idempProp)
  where
    idempProp :: Property
    idempProp = checkProperty (idempotenceCases f isPadding)

{-| Checks that the provided 'ByteString' is an absorbing element for the
given 'DefaultFun', under the given semantics. Specifically, given @f@
as the operation and @0@ as the absorbing element, for any @x@,
@f x 0 = f 0 x = 0@. -}
absorbtionLaw :: String -> UPLC.DefaultFun -> Bool -> ByteString -> TestTree
absorbtionLaw name f isPadding absorber =
  testPropertyNamed
    ("absorbing element (" <> name <> ")")
    ("absorbing_element_" <> fromString name)
    (mapTestLimitAtLeast 75 (`div` 15) absorbProp)
  where
    absorbProp :: Property
    absorbProp = checkProperty (absorbtionCases f isPadding absorber)

-- Helpers

leftDistProp :: UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> Property
leftDistProp f distOp isPadding = checkProperty (leftDistCases f distOp isPadding)

rightDistProp :: UPLC.DefaultFun -> Bool -> Property
rightDistProp f isPadding = checkProperty (rightDistCases f isPadding)

commProp :: UPLC.DefaultFun -> Bool -> Property
commProp f isPadding = checkProperty (commCases f isPadding)

assocProp :: UPLC.DefaultFun -> Bool -> Property
assocProp f isPadding = checkProperty (assocCases f isPadding)

unitProp :: UPLC.DefaultFun -> Bool -> ByteString -> Property
unitProp f isPadding unit = checkProperty (unitCases f isPadding unit)

genIndexOf :: ByteString -> Gen Integer
genIndexOf bs = Gen.integral . Range.linear 0 . fromIntegral $ BS.length bs * 8 - 1

genListsOfIndices :: ByteString -> Gen [Integer]
genListsOfIndices bs = do
  ourLen :: Int <- Gen.integral . Range.linear 0 $ 8 * len - 1
  ixes <- Gen.list (Range.singleton ourLen) $ genIndex
  pure ixes
  where
    len :: Int
    len = BS.length bs
    genIndex :: Gen Integer
    genIndex = Gen.integral . Range.linear 0 . fromIntegral $ len * 8 - 1

-- Shared case generators: normal tests assert the checks; export only consumes their terms.

replicateIndexCases :: Gen Check
replicateIndexCases = do
  n <- Gen.integral . Range.linear 1 $ 512
  b <- Gen.integral . Range.constant 0 $ 255
  i <- Gen.integral . Range.linear 0 $ n - 1
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () n
          , mkConstant @Integer () b
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.IndexByteString)
          [ lhsInner
          , mkConstant @Integer () i
          ]
  checkConstant @Integer b lhs

getSetCases :: Gen Check
getSetCases = do
  bs <- genByteString 1 512
  i <- genIndexOf bs
  let lookupExp =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ mkConstant @ByteString () bs
          , mkConstant @Integer () i
          ]
  -- Compute the next input without evaluating a builtin during generation.
  -- The normal test also checks that ReadBit agrees with this reference.
  let b = Bits.testBit (BS.index bs (BS.length bs - 1 - fromInteger (i `div` 8))) (fromInteger (i `mod` 8))
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () [i]
          , mkConstant @Bool () b
          ]
  CheckBoth <$> checkConstant b lookupExp <*> checkConstant bs lhs

setGetCases :: Gen Check
setGetCases = do
  bs <- genByteString 1 512
  i <- genIndexOf bs
  b <- Gen.bool
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () [i]
          , mkConstant @Bool () b
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ReadBit)
          [ lhsInner
          , mkConstant @Integer () i
          ]
  checkConstant b lhs

setSetCases :: Gen Check
setSetCases = do
  bs <- genByteString 1 512
  i <- genIndexOf bs
  b1 <- Gen.bool
  b2 <- Gen.bool
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () [i, i]
          , mkConstant @Bool () b1
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ lhsInner
          , mkConstant @[Integer] () [i, i]
          , mkConstant @Bool () b2
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () [i]
          , mkConstant @Bool () b2
          ]
  checkSame lhs rhs

writeBitsIdentityCases :: Bool -> Gen Check
writeBitsIdentityCases b = do
  bs <- genByteString 1 512
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () []
          , mkConstant @Bool () b
          ]
  checkConstant bs lhs

writeBitsCompositionCases :: Bool -> Gen Check
writeBitsCompositionCases b = do
  bs <- genByteString 1 512
  ixes1 <- genListsOfIndices bs
  ixes2 <- genListsOfIndices bs
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () ixes1
          , mkConstant @Bool () b
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ lhsInner
          , mkConstant @[Integer] () ixes2
          , mkConstant @Bool () b
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.WriteBits)
          [ mkConstant @ByteString () bs
          , mkConstant @[Integer] () (ixes1 <> ixes2)
          , mkConstant @Bool () b
          ]
  checkSame lhs rhs

replicateIdentityCases :: Gen Check
replicateIdentityCases = do
  b <- Gen.integral . Range.constant 0 $ 255
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () 0
          , mkConstant @Integer () b
          ]
  checkConstant @ByteString "" lhs

replicateCompositionCases :: Gen Check
replicateCompositionCases = do
  b <- Gen.integral . Range.constant 0 $ 255
  n1 <- Gen.integral . Range.linear 0 $ 512
  n2 <- Gen.integral . Range.linear 0 $ 512
  let lhsInner1 =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () n1
          , mkConstant @Integer () b
          ]
  let lhsInner2 =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () n2
          , mkConstant @Integer () b
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.AppendByteString)
          [ lhsInner1
          , lhsInner2
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () PLC.ReplicateByte)
          [ mkConstant @Integer () (n1 + n2)
          , mkConstant @Integer () b
          ]
  checkSame lhs rhs

complementSelfInverseCases :: Gen Check
complementSelfInverseCases = do
  bs <- genByteString 0 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ mkConstant @ByteString () bs
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ lhsInner
          ]
  checkConstant bs lhs

deMorganCases :: UPLC.DefaultFun -> UPLC.DefaultFun -> Gen Check
deMorganCases f g = do
  semantics <- Gen.bool
  bs1 <- genByteString 0 512
  bs2 <- genByteString 0 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () semantics
          , mkConstant @ByteString () bs1
          , mkConstant @ByteString () bs2
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ lhsInner
          ]
  let rhsInner1 =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ mkConstant @ByteString () bs1
          ]
  let rhsInner2 =
        mkIterAppNoAnn
          (builtin () PLC.ComplementByteString)
          [ mkConstant @ByteString () bs2
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () g)
          [ mkConstant @Bool () semantics
          , rhsInner1
          , rhsInner2
          ]
  checkSame lhs rhs

xorInvoluteLawCases :: Gen Check
xorInvoluteLawCases = do
  bs <- genByteString 0 512
  semantics <- Gen.bool
  let lhsInner =
        mkIterAppNoAnn
          (builtin () PLC.XorByteString)
          [ mkConstant @Bool () semantics
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () bs
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () PLC.XorByteString)
          [ mkConstant @Bool () semantics
          , mkConstant @ByteString () bs
          , lhsInner
          ]
  checkConstant bs lhs

idempotenceCases :: UPLC.DefaultFun -> Bool -> Gen Check
idempotenceCases f isPadding = do
  bs <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () bs
          ]
  checkConstant bs lhs

absorbtionCases :: UPLC.DefaultFun -> Bool -> ByteString -> Gen Check
absorbtionCases f isPadding absorber = do
  bs <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () absorber
          ]
  checkConstant absorber lhs

leftDistCases :: UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> Gen Check
leftDistCases f distOp isPadding = do
  x <- genByteString 0 512
  y <- genByteString 0 512
  z <- genByteString 0 512
  let distLhs =
        mkIterAppNoAnn
          (builtin () distOp)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () y
          , mkConstant @ByteString () z
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () x
          , distLhs
          ]
  let distRhs1 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () x
          , mkConstant @ByteString () y
          ]
  let distRhs2 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () x
          , mkConstant @ByteString () z
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () distOp)
          [ mkConstant @Bool () isPadding
          , distRhs1
          , distRhs2
          ]
  checkSame lhs rhs

rightDistCases :: UPLC.DefaultFun -> Bool -> Gen Check
rightDistCases f isPadding = do
  x <- genByteString 0 512
  y <- genByteString 0 512
  z <- genByteString 0 512
  let lhsInner =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () x
          , mkConstant @ByteString () y
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , lhsInner
          , mkConstant @ByteString () z
          ]
  let rhsInner1 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () x
          , mkConstant @ByteString () z
          ]
  let rhsInner2 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () y
          , mkConstant @ByteString () z
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , rhsInner1
          , rhsInner2
          ]
  checkSame lhs rhs

commCases :: UPLC.DefaultFun -> Bool -> Gen Check
commCases f isPadding = do
  data1 <- genByteString 0 512
  data2 <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () data1
          , mkConstant @ByteString () data2
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () data2
          , mkConstant @ByteString () data1
          ]
  checkSame lhs rhs

assocCases :: UPLC.DefaultFun -> Bool -> Gen Check
assocCases f isPadding = do
  data1 <- genByteString 0 512
  data2 <- genByteString 0 512
  data3 <- genByteString 0 512
  let data12 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () data1
          , mkConstant @ByteString () data2
          ]
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , data12
          , mkConstant @ByteString () data3
          ]
  let data23 =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () data2
          , mkConstant @ByteString () data3
          ]
  let rhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () data1
          , data23
          ]
  checkSame lhs rhs

unitCases :: UPLC.DefaultFun -> Bool -> ByteString -> Gen Check
unitCases f isPadding unit = do
  bs <- genByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () unit
          ]
  checkConstant bs lhs

-- | Emit cases for each law and builtin/semantics combination in the normal suite.
generate_bitwise_cip0122_properties :: OutputFormat -> FilePath -> Int -> QCGen -> IO ()
generate_bitwise_cip0122_properties format outputDir numFiles seed =
  mapM_
    (\(name, gen) -> generateBitwisePropertyFiles format suiteDir numFiles seed name gen)
    conformanceProperties
  where
    suiteDir = outputDir </> "bitwise" </> "CIP0122"

-- Names identify the Haskell property, plus its parameters where needed to
-- distinguish instantiations. Keep the combinations aligned with test_Bitwise_CIP0122.
conformanceProperties :: [(String, Gen Check)]
conformanceProperties =
  concat
    [ [ ("commProp_" <> name <> "_" <> semantics, commCases fun padding)
      , ("assocProp_" <> name <> "_" <> semantics, assocCases fun padding)
      ]
    | (name, fun) <- logicalBuiltins
    , (semantics, padding) <- [("truncation", False), ("padding", True)]
    ]
    <> [ ("unitProp_" <> name <> "_padding", unitCases fun True "")
       | (name, fun) <- logicalBuiltins
       ]
    <> [ ("absorbtionLaw_" <> name <> "_truncation", absorbtionCases fun False "")
       | (name, fun) <- logicalBuiltins
       ]
    <> concat
      [ [ ("idempotenceLaw_" <> name <> "_truncation", idempotenceCases fun False)
        , ("leftDistProp_" <> name <> "_itself_truncation", leftDistCases fun fun False)
        , ("leftDistProp_" <> name <> "_itself_padding", leftDistCases fun fun True)
        , ("rightDistProp_" <> name <> "_padding", rightDistCases fun True)
        ]
      | (name, fun) <- [("andByteString", PLC.AndByteString), ("orByteString", PLC.OrByteString)]
      ]
    <> [
         ( "leftDistProp_andByteString_orByteString_truncation"
         , leftDistCases PLC.AndByteString PLC.OrByteString False
         )
       ,
         ( "leftDistProp_andByteString_xorByteString_truncation"
         , leftDistCases PLC.AndByteString PLC.XorByteString False
         )
       ,
         ( "leftDistProp_orByteString_andByteString_truncation"
         , leftDistCases PLC.OrByteString PLC.AndByteString False
         )
       , ("xorInvoluteLaw", xorInvoluteLawCases)
       , ("complementSelfInverse", complementSelfInverseCases)
       , ("deMorgan_andByteString", deMorganCases PLC.AndByteString PLC.OrByteString)
       , ("deMorgan_orByteString", deMorganCases PLC.OrByteString PLC.AndByteString)
       , ("getSet", getSetCases)
       , ("setGet", setGetCases)
       , ("setSet", setSetCases)
       , ("writeBitsHomomorphismLaws_identityProp_false", writeBitsIdentityCases False)
       , ("writeBitsHomomorphismLaws_identityProp_true", writeBitsIdentityCases True)
       , ("writeBitsHomomorphismLaws_compositionProp_false", writeBitsCompositionCases False)
       , ("writeBitsHomomorphismLaws_compositionProp_true", writeBitsCompositionCases True)
       , ("replicateHomomorphismLaws_identityProp", replicateIdentityCases)
       , ("replicateHomomorphismLaws_compositionProp", replicateCompositionCases)
       , ("replicateIndex", replicateIndexCases)
       ]
  where
    logicalBuiltins =
      [ ("andByteString", PLC.AndByteString)
      , ("orByteString", PLC.OrByteString)
      , ("xorByteString", PLC.XorByteString)
      ]
