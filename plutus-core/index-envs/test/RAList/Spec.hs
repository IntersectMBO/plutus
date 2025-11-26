{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module RAList.Spec (tests) where

import Control.Exception
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromJust, isNothing)
import Data.Proxy
import Data.RandomAccessList.Class as RAL
import Data.RandomAccessList.RelativizedMap qualified as RM
import Data.RandomAccessList.SkewBinary qualified as B
import Data.RandomAccessList.SkewBinarySlab qualified as BS
import Data.Vector.NonEmpty qualified as NEV
import GHC.Exts
import Test.QuickCheck.Gen
import Test.QuickCheck.Instances ()
import Test.Tasty
import Test.Tasty.QuickCheck

instance (Element e ~ a, RandomAccessList e, Arbitrary a) => Arbitrary (AsRAL e) where
  arbitrary = fromList <$> arbitrary

deriving via (AsRAL (B.RAList a)) instance Arbitrary a => Arbitrary (B.RAList a)
deriving via (AsRAL (RM.RelativizedMap a)) instance Arbitrary a => Arbitrary (RM.RelativizedMap a)

{-| The other RALs have unique representations for a given size, so generating them
from equivalent lists is fine. This isn't true for the slab version! So we write
a manual generator that appends stuff randomly as slabs or not. -}
instance Arbitrary a => Arbitrary (BS.RAList a) where
  arbitrary = sized $ \sz -> go sz empty
    where
      go :: Int -> BS.RAList a -> Gen (BS.RAList a)
      go 0 acc = pure acc
      go sz acc = do
        toAdd <- choose (1, sz)
        elemsToAdd <- vector toAdd
        asSlab <- arbitrary
        let extended =
              if asSlab
                then RAL.consSlab (fromJust $ NEV.fromList elemsToAdd) acc
                else List.foldl' (\env val -> RAL.cons val env) acc elemsToAdd
        go (sz - toAdd) extended

type RALTestable e a =
  ( a ~ Element e
  , RandomAccessList e
  , Eq a
  , Eq e
  , Show a
  , Show e
  , Arbitrary a
  , Arbitrary e
  , IsList e
  , Item e ~ a
  )

sameModuloExceptions :: Eq a => IO a -> IO a -> IO Bool
sameModuloExceptions a1 a2 = do
  i1 <- try @SomeException $ a1
  i2 <- try @SomeException $ a2
  pure $ case (i1, i2) of
    (Left _, Left _) -> False
    (Right v1, Right v2) -> v1 == v2
    _ -> False

prop_fromToList :: forall e a. RALTestable e a => Proxy e -> Property
prop_fromToList _ = forAll arbitrary $ \(l :: e) -> (fromList $ toList l) === l

prop_toFromList :: forall e a. RALTestable e a => Proxy e -> Property
prop_toFromList _ = forAll arbitrary $ \(l :: [a]) -> (toList $ fromList @e l) === l

prop_empty :: forall e a. RALTestable e a => Proxy e -> Property
prop_empty _ = fromList @e empty === empty

prop_cons :: forall e a. RALTestable e a => Proxy e -> Property
prop_cons _ = forAll arbitrary $ \(l :: e, e :: a) -> cons e (toList l) === toList (cons e l)

prop_uncons :: forall e a. RALTestable e a => Proxy e -> Property
prop_uncons _ =
  forAll arbitrary $ \(l :: e) -> uncons (toList l) === (fmap $ fmap toList) (uncons l)

prop_length :: forall e a. RALTestable e a => Proxy e -> Property
prop_length _ = forAll arbitrary $ \(l :: e) -> RAL.length (toList l) === RAL.length l

-- Includes some out-of-range indices above the length
prop_indexZero :: forall e a. RALTestable e a => Proxy e -> Property
prop_indexZero _ =
  forAll arbitrary $ \(l :: e) -> forAll (chooseWord64 (0, 2 * (RAL.length l - 1))) $ \i ->
    let r1 = indexZero (toList l) i
        r2 = indexZero l i
     in cover 10 (isNothing r1) "failed lookups" $ r1 == r2

-- Includes some out-of-range indices above the length
prop_unsafeIndexZero :: forall e a. RALTestable e a => Proxy e -> Property
prop_unsafeIndexZero _ =
  forAll arbitrary $ \(l :: e) -> forAll (chooseWord64 (0, 2 * (RAL.length l - 1))) $ \i ->
    ioProperty $ sameModuloExceptions (evaluate $ indexZero (toList l) i) (evaluate $ indexZero l i)

-- Includes some out-of-range indices above the length, and 0 which is out-of-range below
prop_indexOne :: forall e a. RALTestable e a => Proxy e -> Property
prop_indexOne _ =
  forAll arbitrary $ \(l :: e) -> forAll (chooseWord64 (0, 2 * (RAL.length l - 1))) $ \i ->
    let r1 = indexOne (toList l) i
        r2 = indexOne l i
     in cover 10 (isNothing r1) "failed lookups" $ r1 == r2

-- Includes some out-of-range indices above the length, and 0 which is out-of-range below
prop_unsafeIndexOne :: forall e a. RALTestable e a => Proxy e -> Property
prop_unsafeIndexOne _ =
  forAll arbitrary $ \(l :: e) -> forAll (chooseWord64 (0, 2 * (RAL.length l - 1))) $ \i ->
    ioProperty $
      sameModuloExceptions (evaluate $ indexOne (toList l) i) (evaluate $ indexOne l i)

prop_consSlab :: forall e a. RALTestable e a => Proxy e -> Property
prop_consSlab _ = forAll arbitrary $ \(l :: e, es :: NonEmpty a) ->
  let nev = NEV.fromNonEmpty es
   in cover 90 (NEV.length nev > 1) "non-trivial" $
        consSlab nev (toList l) === toList (consSlab nev l)

prop_indexOneZero :: forall e a. RALTestable e a => Proxy e -> Property
prop_indexOneZero _ =
  forAll arbitrary $ \(l :: e) -> forAll (chooseWord64 (0, 2 * (RAL.length l - 1))) $ \i ->
    let r1 = indexZero (toList l) i
        r2 = indexOne l (i + 1)
     in cover 10 (isNothing r1) "failed lookups" $ r1 === r2

{-| These properties test the correctness of each RAL function by checking that it behaves the same
as the canonical version of that function on lists. In combination with a test that to/fromList
form an isomorphism, this assures us that each function is correct. -}
ralProps :: forall e a. RALTestable e a => Proxy e -> TestTree
ralProps p =
  localOption (QuickCheckTests 10000) $
    testGroup
      "RandomAccessList correctness properties"
      [ testGroup
          "to/fromList is an isomorphism"
          [ testProperty "fromList . toList == id" $ prop_fromToList p
          , testProperty "toList . fromList == id" $ prop_toFromList p
          ]
      , testGroup
          "operations"
          [ testProperty "empty" $ prop_empty p
          , testProperty "cons" $ prop_cons p
          , testProperty "uncons" $ prop_uncons p
          , testProperty "length" $ prop_length p
          , testProperty "indexZero" $ prop_indexZero p
          , testProperty "unsafeIndexZero" $ prop_unsafeIndexZero p
          , testProperty "indexOne" $ prop_indexOne p
          , testProperty "unsafeIndexOne" $ prop_unsafeIndexOne p
          , testProperty "consSlab" $ prop_consSlab p
          ]
      , testProperty "indexOne indexZero coherence" $ prop_indexOneZero p
      ]

tests :: TestTree
tests =
  testGroup
    "RandomAccessLists"
    [ testGroup
        "SkewBinary"
        [ralProps (Proxy :: (Proxy (B.RAList Integer)))]
    , testGroup
        "SkewBinarySlab"
        [ralProps (Proxy :: (Proxy (BS.RAList Integer)))]
    , testGroup
        "RelativizedMap"
        [ralProps (Proxy :: (Proxy (RM.RelativizedMap Integer)))]
    ]
