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
  ) where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusCore.Test (mapTestLimitAtLeast)
import UntypedPlutusCore qualified as UPLC

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Evaluation.Helpers
  ( evaluateTheSame
  , evaluateToHaskell
  , evaluatesToConstant
  , forAllByteString
  )
import GHC.Exts (fromString)
import Hedgehog (Gen, Property, PropertyT, forAll, forAllWith, property)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)

{-| Any call to 'replicateByteString' must produce the same byte at
every valid index, namely the byte specified. -}
replicateIndex :: TestTree
replicateIndex = testPropertyNamed "every byte is the same" "replicate_all_match" $
  mapTestLimitAtLeast 99 (`div` 20) . property $ do
    n <- forAll . Gen.integral . Range.linear 1 $ 512
    b <- forAll . Gen.integral . Range.constant 0 $ 255
    i <- forAll . Gen.integral . Range.linear 0 $ n - 1
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
    evaluatesToConstant @Integer b lhs

{-| If you retrieve a bit value at an index, then write that same value to
the same index, nothing should happen. -}
getSet :: TestTree
getSet =
  testPropertyNamed "get-set" "get_set" . mapTestLimitAtLeast 50 (`div` 20) . property $ do
    bs <- forAllByteString 1 512
    i <- forAllIndexOf bs
    let lookupExp =
          mkIterAppNoAnn
            (builtin () PLC.ReadBit)
            [ mkConstant @ByteString () bs
            , mkConstant @Integer () i
            ]
    b <- evaluateToHaskell lookupExp
    let lhs =
          mkIterAppNoAnn
            (builtin () PLC.WriteBits)
            [ mkConstant @ByteString () bs
            , mkConstant @[Integer] () [i]
            , mkConstant @Bool () b
            ]
    evaluatesToConstant bs lhs

{-| If you write a bit value to an index, then retrieve the bit value at the
same index, you should get back what you wrote. -}
setGet :: TestTree
setGet =
  testPropertyNamed "set-get" "set_get" . mapTestLimitAtLeast 99 (`div` 10) . property $ do
    bs <- forAllByteString 1 512
    i <- forAllIndexOf bs
    b <- forAll Gen.bool
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
    evaluatesToConstant b lhs

-- | If you write twice to the same bit index, the second write should win.
setSet :: TestTree
setSet =
  testPropertyNamed "set-set" "set_set" . mapTestLimitAtLeast 50 (`div` 20) . property $ do
    bs <- forAllByteString 1 512
    i <- forAllIndexOf bs
    b1 <- forAll Gen.bool
    b2 <- forAll Gen.bool
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
    evaluateTheSame lhs rhs

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
    identityProp b = property $ do
      bs <- forAllByteString 1 512
      let lhs =
            mkIterAppNoAnn
              (builtin () PLC.WriteBits)
              [ mkConstant @ByteString () bs
              , mkConstant @[Integer] () []
              , mkConstant @Bool () b
              ]
      evaluatesToConstant bs lhs
    compositionProp :: Bool -> Property
    compositionProp b = property $ do
      bs <- forAllByteString 1 512
      ixes1 <- forAllListsOfIndices bs
      ixes2 <- forAllListsOfIndices bs
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
      evaluateTheSame lhs rhs

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
    identityProp = property $ do
      b <- forAll . Gen.integral . Range.constant 0 $ 255
      let lhs =
            mkIterAppNoAnn
              (builtin () PLC.ReplicateByte)
              [ mkConstant @Integer () 0
              , mkConstant @Integer () b
              ]
      evaluatesToConstant @ByteString "" lhs
    compositionProp :: Property
    compositionProp = property $ do
      b <- forAll . Gen.integral . Range.constant 0 $ 255
      n1 <- forAll . Gen.integral . Range.linear 0 $ 512
      n2 <- forAll . Gen.integral . Range.linear 0 $ 512
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
      evaluateTheSame lhs rhs

-- | If you complement a 'ByteString' twice, nothing should change.
complementSelfInverse :: TestTree
complementSelfInverse =
  testPropertyNamed "self-inverse" "self_inverse" $
    mapTestLimitAtLeast 99 (`div` 20) . property $ do
      bs <- forAllByteString 0 512
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
      evaluatesToConstant bs lhs

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
    go f g = mapTestLimitAtLeast 50 (`div` 10) . property $ do
      semantics <- forAllWith showSemantics Gen.bool
      bs1 <- forAllByteString 0 512
      bs2 <- forAllByteString 0 512
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
      evaluateTheSame lhs rhs

-- | If you XOR any 'ByteString' with itself twice, nothing should change.
xorInvoluteLaw :: TestTree
xorInvoluteLaw = testPropertyNamed "involute (both)" "involute_both" $
  mapTestLimitAtLeast 99 (`div` 20) . property $ do
    bs <- forAllByteString 0 512
    semantics <- forAllWith showSemantics Gen.bool
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
    evaluatesToConstant bs lhs

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
    idempProp = property $ do
      bs <- forAllByteString 0 512
      let lhs =
            mkIterAppNoAnn
              (builtin () f)
              [ mkConstant @Bool () isPadding
              , mkConstant @ByteString () bs
              , mkConstant @ByteString () bs
              ]
      evaluatesToConstant bs lhs

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
    absorbProp = property $ do
      bs <- forAllByteString 0 512
      let lhs =
            mkIterAppNoAnn
              (builtin () f)
              [ mkConstant @Bool () isPadding
              , mkConstant @ByteString () bs
              , mkConstant @ByteString () absorber
              ]
      evaluatesToConstant absorber lhs

-- Helpers

showSemantics :: Bool -> String
showSemantics b =
  if b
    then "padding semantics"
    else "truncation semantics"

leftDistProp :: UPLC.DefaultFun -> UPLC.DefaultFun -> Bool -> Property
leftDistProp f distOp isPadding = property $ do
  x <- forAllByteString 0 512
  y <- forAllByteString 0 512
  z <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

rightDistProp :: UPLC.DefaultFun -> Bool -> Property
rightDistProp f isPadding = property $ do
  x <- forAllByteString 0 512
  y <- forAllByteString 0 512
  z <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

commProp :: UPLC.DefaultFun -> Bool -> Property
commProp f isPadding = property $ do
  data1 <- forAllByteString 0 512
  data2 <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

assocProp :: UPLC.DefaultFun -> Bool -> Property
assocProp f isPadding = property $ do
  data1 <- forAllByteString 0 512
  data2 <- forAllByteString 0 512
  data3 <- forAllByteString 0 512
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
  evaluateTheSame lhs rhs

unitProp :: UPLC.DefaultFun -> Bool -> ByteString -> Property
unitProp f isPadding unit = property $ do
  bs <- forAllByteString 0 512
  let lhs =
        mkIterAppNoAnn
          (builtin () f)
          [ mkConstant @Bool () isPadding
          , mkConstant @ByteString () bs
          , mkConstant @ByteString () unit
          ]
  evaluatesToConstant bs lhs

forAllIndexOf :: ByteString -> PropertyT IO Integer
forAllIndexOf bs = forAll . Gen.integral . Range.linear 0 . fromIntegral $ BS.length bs * 8 - 1

forAllListsOfIndices :: ByteString -> PropertyT IO [Integer]
forAllListsOfIndices bs = do
  ourLen :: Int <- forAll . Gen.integral . Range.linear 0 $ 8 * len - 1
  ixes <- forAll . Gen.list (Range.singleton ourLen) $ genIndex
  pure ixes
  where
    len :: Int
    len = BS.length bs
    genIndex :: Gen Integer
    genIndex = Gen.integral . Range.linear 0 . fromIntegral $ len * 8 - 1
