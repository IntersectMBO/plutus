{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}
module Foundation.Check.Arbitrary
    ( Arbitrary(..)
    , frequency
    , oneof
    , elements
    , between
    ) where

import           Basement.Imports
import           Foundation.Primitive
import           Basement.Nat
import           Basement.Cast (cast)
import           Basement.IntegralConv
import           Basement.Bounded
import           Basement.Types.OffsetSize
import qualified Basement.Types.Char7 as Char7
import           Basement.Types.Word128 (Word128(..))
import           Basement.Types.Word256 (Word256(..))
#if __GLASGOW_HASKELL__ >= 710
import qualified Basement.Sized.List as ListN
#endif
import           Foundation.Check.Gen
import           Foundation.Random
import           Foundation.Bits
import           Foundation.Collection
import           Foundation.Numerical
import           Control.Monad (replicateM)

-- | How to generate an arbitrary value for 'a'
class Arbitrary a where
    arbitrary :: Gen a

instance Arbitrary Integer where
    arbitrary = arbitraryInteger
instance Arbitrary Natural where
    arbitrary = arbitraryNatural

instance (NatWithinBound Word64 n, KnownNat n) => Arbitrary (Zn64 n) where
    arbitrary = zn64 <$> arbitrary
instance KnownNat n => Arbitrary (Zn n) where
    arbitrary = zn <$> arbitraryNatural

-- prim types
instance Arbitrary Int where
    arbitrary = int64ToInt <$> arbitraryInt64
instance Arbitrary Word where
    arbitrary = word64ToWord <$> arbitraryWord64
instance Arbitrary Word256 where
    arbitrary = Word256 <$> arbitraryWord64 <*> arbitraryWord64 <*> arbitraryWord64 <*> arbitraryWord64
instance Arbitrary Word128 where
    arbitrary = Word128 <$> arbitraryWord64 <*> arbitraryWord64
instance Arbitrary Word64 where
    arbitrary = arbitraryWord64
instance Arbitrary Word32 where
    arbitrary = integralDownsize <$> arbitraryWord64
instance Arbitrary Word16 where
    arbitrary = integralDownsize <$> arbitraryWord64
instance Arbitrary Word8 where
    arbitrary = integralDownsize <$> arbitraryWord64
instance Arbitrary Int64 where
    arbitrary = arbitraryInt64
instance Arbitrary Int32 where
    arbitrary = integralDownsize <$> arbitraryInt64
instance Arbitrary Int16 where
    arbitrary = integralDownsize <$> arbitraryInt64
instance Arbitrary Int8 where
    arbitrary = integralDownsize <$> arbitraryInt64
instance Arbitrary Char where
    arbitrary = arbitraryChar
instance Arbitrary Char7 where
    arbitrary = Char7.fromByteMask . integralDownsize <$> arbitraryWord64
instance Arbitrary (CountOf ty) where
    arbitrary = CountOf <$> arbitrary

instance Arbitrary Bool where
    arbitrary = flip testBit 0 <$> arbitraryWord64

instance Arbitrary String where
    arbitrary = genWithParams $ \params ->
        fromList <$> (genMax (genMaxSizeString params) >>= \i -> replicateM (cast i) arbitrary)

instance Arbitrary AsciiString where
    arbitrary = genWithParams $ \params ->
        fromList <$> (genMax (genMaxSizeString params) >>= \i -> replicateM (cast i) arbitrary)

instance Arbitrary Float where
    arbitrary = arbitraryF32
instance Arbitrary Double where
    arbitrary = arbitraryF64

instance Arbitrary a => Arbitrary (Maybe a) where
    arbitrary = frequency $ nonEmpty_ [ (1, pure Nothing), (4, Just <$> arbitrary) ]

instance (Arbitrary l, Arbitrary r) => Arbitrary (Either l r) where
    arbitrary = oneof $ nonEmpty_ [ Left <$> arbitrary, Right <$> arbitrary ]

instance (Arbitrary a, Arbitrary b)
    => Arbitrary (a,b) where
    arbitrary = (,) <$> arbitrary <*> arbitrary
instance (Arbitrary a, Arbitrary b, Arbitrary c)
    => Arbitrary (a,b,c) where
    arbitrary = (,,) <$> arbitrary <*> arbitrary <*> arbitrary
instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d)
    => Arbitrary (a,b,c,d) where
    arbitrary = (,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d, Arbitrary e)
    => Arbitrary (a,b,c,d,e) where
    arbitrary = (,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d, Arbitrary e, Arbitrary f)
    => Arbitrary (a,b,c,d,e,f) where
    arbitrary = (,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary [a] where
    arbitrary = genWithParams $ \params ->
        fromList <$> (genMax (genMaxSizeArray params) >>= \i -> replicateM (cast i) arbitrary)
#if __GLASGOW_HASKELL__ >= 710
instance (Arbitrary a, KnownNat n, NatWithinBound Int n) => Arbitrary (ListN.ListN n a) where
    arbitrary = ListN.replicateM arbitrary
#endif

arbitraryInteger :: Gen Integer
arbitraryInteger =
    -- TODO use the sized parameter
    frequency $ nonEmpty_
        [ (4, integerOfSize True 2)
        , (4, integerOfSize False 2)
        , (4, integerOfSize True 4)
        , (4, integerOfSize False 4)
        , (2, integerOfSize True 8)
        , (2, integerOfSize False 8)
        , (1, integerOfSize True 16)
        , (1, integerOfSize False 16)
        ]
  where
    integerOfSize :: Bool -> Word -> Gen Integer
    integerOfSize toSign n = ((if toSign then negate else id) . foldl' (\x y -> x + integralUpsize y) 0 . toList)
                         <$> (arbitraryUArrayOf n :: Gen (UArray Word8))

arbitraryNatural :: Gen Natural
arbitraryNatural = integralDownsize . abs <$> arbitraryInteger

arbitraryChar :: Gen Char
arbitraryChar = frequency $ nonEmpty_
    [ (6, wordToChar <$> genMax 128)
    , (1, wordToChar <$> genMax 0x10ffff)
    ]

arbitraryWord64 :: Gen Word64
arbitraryWord64 = genWithRng getRandomWord64

arbitraryInt64 :: Gen Int64
arbitraryInt64 = cast <$> arbitraryWord64

arbitraryF64 :: Gen Double
arbitraryF64 = genWithRng getRandomF64

arbitraryF32 :: Gen Float
arbitraryF32 = genWithRng getRandomF32

arbitraryUArrayOf :: (PrimType ty, Arbitrary ty) => Word -> Gen (UArray ty)
arbitraryUArrayOf size = between (0, size) >>=
    \sz -> fromList <$> replicateM (cast sz) arbitrary

-- | Call one of the generator weighted
frequency :: NonEmpty [(Word, Gen a)] -> Gen a
frequency (getNonEmpty -> l) = between (0, sum) >>= pickOne l
  where
    sum :: Word
    !sum = foldl' (+) 0 $ fmap fst l

    pickOne ((k,x):xs) n
        | n <= k    = x
        | otherwise = pickOne xs (n-k)
    pickOne _ _ = error "frequency"

oneof :: NonEmpty [Gen a] -> Gen a
oneof ne = frequency (nonEmptyFmap (\x -> (1, x)) ne)

elements :: NonEmpty [a] -> Gen a
elements l = frequency (nonEmptyFmap (\x -> (1, pure x)) l)

between :: (Word, Word) -> Gen Word
between (x,y)
    | range == 0 = pure x
    | otherwise = (+) x <$> genMax range
  where range = y - x

genMax :: Word -> Gen Word
genMax m = flip mod m <$> arbitrary
