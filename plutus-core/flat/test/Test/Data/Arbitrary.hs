{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Data.Arbitrary where
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.ByteString.Short qualified as SBS
import Data.Text qualified as TS
import Data.Text.Lazy qualified as TL
import Test.Data
import Test.Tasty.QuickCheck
-- import           Data.DeriveTH

-- #if MIN_VERSION_base(4,9,0)
import Data.List.NonEmpty qualified as BI
-- #endif

import Numeric.Natural (Natural)

#if MIN_VERSION_base(4,8,0) && MIN_VERSION_QuickCheck(2,10,0)
instance Arbitrary a => Arbitrary (BI.NonEmpty a) where
  arbitrary = BI.fromList . getNonEmpty <$> (arbitrary :: Gen (NonEmptyList a))
  shrink xs = BI.fromList <$> shrink (BI.toList xs)

instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink    = shrinkIntegral
#endif

-- Copied from quickcheck-instances (not used directly as it requires old-time that is incompatible with ghcjs)

instance Arbitrary BS.ByteString where
  arbitrary = BS.pack <$> arbitrary
  shrink xs = BS.pack <$> shrink (BS.unpack xs)

instance Arbitrary BL.ByteString where
  arbitrary = BL.pack <$> arbitrary
  shrink xs = BL.pack <$> shrink (BL.unpack xs)

instance Arbitrary SBS.ShortByteString where
  arbitrary = SBS.pack <$> arbitrary
  shrink xs = SBS.pack <$> shrink (SBS.unpack xs)

-- instance Arbitrary TS.Text where
--     arbitrary = TS.pack <$> arbitrary
--     shrink xs = TS.pack <$> shrink (TS.unpack xs)

-- instance Arbitrary TL.Text where
--     arbitrary = TL.pack <$> arbitrary
--     shrink xs = TL.pack <$> shrink (TL.unpack xs)

-- xxx = generate (arbitrary :: Gen (Large (Int)))

{-
-- derive makeArbitrary ''N
derive makeArbitrary ''Tree

derive makeArbitrary ''List

derive makeArbitrary ''Unit

derive makeArbitrary ''Un

derive makeArbitrary ''A

derive makeArbitrary ''B
-}
-- instance Arbitrary Word7 where arbitrary  = toEnum <$> choose (0, 127)
-- derive makeArbitrary ''ASCII
-- To generate Arbitrary instances while avoiding a direct dependency on 'derive' (that is not supported by Eta)

-- , run in the project directory:  derive -a test/Test/Data.hs --derive=Arbitrary
{-!
deriving instance Arbitrary N
deriving instance Arbitrary Tree
deriving instance Arbitrary List
deriving instance Arbitrary Unit
deriving instance Arbitrary Un
deriving instance Arbitrary A
deriving instance Arbitrary B
!-}
-- GENERATED START
instance () => Arbitrary N where
  arbitrary = do
    x <- choose (0 :: Int, 4)
    case x of
      0 -> return One
      1 -> return Two
      2 -> return Three
      3 -> return Four
      4 -> return Five
      _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance (Arbitrary a) => Arbitrary (Tree a) where
  arbitrary = do
    x <- choose (0 :: Int, 1)
    case x of
      0 -> do
        x1 <- arbitrary
        x2 <- arbitrary
        return (Node x1 x2)
      1 -> Leaf <$> arbitrary
      _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance (Arbitrary a) => Arbitrary (List a) where
  arbitrary = do
    x <- choose (0 :: Int, 1)
    case x of
      0 -> do
        x1 <- arbitrary
        x2 <- arbitrary
        return (C x1 x2)
      1 -> return N
      _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary Unit where
  arbitrary = return Unit

instance () => Arbitrary Un where
  arbitrary = Un <$> arbitrary

instance () => Arbitrary A where
  arbitrary = do
    x <- choose (0 :: Int, 1)
    case x of
      0 -> A <$> arbitrary
      1 -> AA <$> arbitrary
      _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary B where
  arbitrary = do
    x <- choose (0 :: Int, 1)
    case x of
      0 -> B <$> arbitrary
      1 -> BB <$> arbitrary
      _ -> error "FATAL ERROR: Arbitrary instance, logic bug"
-- GENERATED STOP
