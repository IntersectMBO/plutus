{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Arbitrary where

import qualified Data.List                   as List

import           Test.QuickCheck             (Arbitrary (..), Gen, Positive (Positive, getPositive), genericShrink,
                                              getOrdered, oneof, resize, sized, suchThat)
import           Test.QuickCheck.Instances   ()

import           PlutusTx                    (Data (B, Constr, I, List, Map))
import           PlutusTx.AssocMap           (Map)
import qualified PlutusTx.AssocMap           as AssocMap (fromList, toList)
import           PlutusTx.Bimap              (Bimap)
import qualified PlutusTx.Bimap              as Bimap
import           PlutusTx.Builtins
import           PlutusTx.Builtins.Internal
import           PlutusTx.NatRatio.Internal  (NatRatio (NatRatio))
import           PlutusTx.Natural.Internal   (Natural (Natural))
import           PlutusTx.NonEmpty           (NonEmpty ((:|)))
import qualified PlutusTx.Ord                as Ord
import qualified PlutusTx.Prelude            as PlutusPrelude
import           PlutusTx.Ratio              (denominator, numerator, (%))
import qualified PlutusTx.Ratio              as Ratio (Rational, fromGHC, toGHC)
import           PlutusTx.Set                (Set)
import qualified PlutusTx.Set                as Set
import           PlutusTx.UniqueMap.Internal (UniqueMap (UniqueMap))

--------------------------------------------------------------------------------
-- Special cases

instance Arbitrary BuiltinByteString where
  arbitrary = BuiltinByteString <$> resize 64 arbitrary
  shrink (BuiltinByteString x) = BuiltinByteString <$> shrink x

instance Arbitrary Data where
  -- ToJSON / FromJSON instances of BuiltinData implemented with serialise / deserialise functions from Codec.Serialise.
  -- In case the length of ByteStrings is more than 64 bytes, deserialization error occurs.
  --
  -- Example:
  -- B "\RS\194w\255$u\144-\191\205u\191\183\&4\232\190\225\249\"}S+\217\ENQf\196\SUB\SI\191\169\149^\DC41n%\252\&1\245wr&\161|OX3\170h7\153\210\225\177\228\233\207\231#\DC1[\191\242\148\210\US\167"
  -- Failed! Exception: 'DeserialiseFailure 69 "ByteString exceeds 64 bytes"'
  --
  -- It goes from the implementation of PlutusCore.Data.decodeBoundedBytes:
  --
  -- @
  -- decodeBoundedBytes :: Decoder s Data
  -- decodeBoundedBytes =  do
  -- b <- CBOR.decodeBytes
  -- if BS.length b <= 64
  --  then pure $ B b
  --  else fail $ "ByteString exceeds 64 bytes"
  -- @
  arbitrary = sized $ oneof . dataGenList
    where
      positive :: Gen Integer
      positive = getPositive <$> arbitrary @(Positive Integer)

      dataGenList :: Int -> [Gen Data]
      dataGenList n
        | n < 2 = [I <$> arbitrary, B <$> arbitrary]
        | otherwise =
          [ I <$> arbitrary
          , B <$> resize 64 arbitrary
          , Map <$> resize (n `div` 2) arbitrary
          , List <$> resize (n `div` 2) arbitrary
          , Constr <$> positive <*> resize (n `div` 2) arbitrary
          ]
  shrink = genericShrink

instance (Arbitrary a, Arbitrary b, Ord.Ord a, Ord.Ord b, Ord a, Ord b) => Arbitrary (Bimap a b) where
  arbitrary = Bimap.fromList . getOrdered <$> arbitrary
  shrink = fmap Bimap.fromList . shrink . Bimap.toList

instance (Arbitrary k, Arbitrary v) => Arbitrary (Map k v) where
  arbitrary = AssocMap.fromList <$> arbitrary
  shrink = fmap AssocMap.fromList . shrink . AssocMap.toList

instance (Arbitrary a) => Arbitrary (NonEmpty a) where
  arbitrary = (:|) <$> arbitrary <*> arbitrary
  shrink (a :| as) = do
    a' <- shrink a
    as' <- shrink as
    pure (a' :| as')

instance Arbitrary Ratio.Rational where
  arbitrary = Ratio.fromGHC <$> arbitrary
  shrink = fmap Ratio.fromGHC . shrink . Ratio.toGHC

instance (Arbitrary a, Ord a, Ord.Ord a) => Arbitrary (Set a) where
  arbitrary = Set.fromList . getOrdered <$> arbitrary
  shrink = fmap Set.fromList . shrink . Set.toList

instance
  (Arbitrary k, Arbitrary v, Ord k) =>
  Arbitrary (UniqueMap k v)
  where
  arbitrary = do
    ks <- List.nub . getOrdered <$> arbitrary
    UniqueMap <$> traverse (\key -> (key,) <$> arbitrary) ks
  shrink (UniqueMap um) = do
    um' <- shrink um
    pure . UniqueMap . List.sortOn Prelude.fst $ um'

instance Arbitrary Natural where
  arbitrary = do
    NonNegative n <- arbitrary
    pure . Natural $ n
  shrink (Natural n) = do
    NonNegative n' <- shrink . NonNegative $ n
    pure . Natural $ n'

instance Arbitrary NatRatio where
  arbitrary = do
    NonNegative num <- arbitrary
    Positive den <- arbitrary
    pure . NatRatio $ num % den
  shrink (NatRatio r) = do
    NonNegative num' <- shrink . NonNegative . numerator $ r
    Positive den' <- shrink . Positive . denominator $ r
    pure . NatRatio $ num' % den'

-- | A newtype which ensures we generate a value that is not 'zero'.
newtype NonZero a = NonZero a
  deriving stock (Show)
  deriving
    ( Eq
    , PlutusPrelude.AdditiveSemigroup
    , PlutusPrelude.AdditiveMonoid
    )
    via a

instance
  (Eq a, PlutusPrelude.AdditiveMonoid a, Arbitrary a) =>
  Arbitrary (NonZero a)
  where
  arbitrary = do
    x <- arbitrary `suchThat` (PlutusPrelude.zero /=)
    pure . NonZero $ x
  shrink (NonZero x) = do
    x' <- filter (PlutusPrelude.zero /=) . shrink $ x
    pure . NonZero $ x'

-- | A newtype which ensures we generate a value that's not less than 'zero'.
newtype NonNegative a = NonNegative a
  deriving stock (Show)
  deriving (Eq) via a

instance
  (Arbitrary a, PlutusPrelude.AdditiveMonoid a, PlutusPrelude.Ord a) =>
  Arbitrary (NonNegative a)
  where
  arbitrary = do
    x <- arbitrary `suchThat` (PlutusPrelude.zero PlutusPrelude.<=)
    pure . NonNegative $ x
  shrink (NonNegative x) = do
    x' <- filter (PlutusPrelude.zero PlutusPrelude.<=) . shrink $ x
    pure . NonNegative $ x'
