{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Test.Foundation.Bits
    ( tests
    ) where

import Basement.Cast
import Foundation.Bits
import Foundation.Check
import Foundation

newtype Shifter = Shifter Int
    deriving (Show,Eq)

instance Arbitrary Shifter where
    arbitrary = Shifter . applyMod <$> arbitrary
      where applyMod i = abs i `mod` 256

testBits :: forall a . (Additive a, Bounded a, Difference a ~ a, Integral a, IsIntegral a, Bits a, Show a, Subtractive a, Eq a, Arbitrary a, Typeable a)
         => String
         -> Proxy a
         -> Gen a
         -> Test
testBits n _ _ = Group n
    [ Property "shiftR" $ \(a :: a) (Shifter i) ->
        (a `shiftR` i) === convertBack (toInteger a `shiftR` i)
    , Property "shiftL" $ \(a :: a) (Shifter i) ->
        (a `shiftL` i) === convertBack (toInteger a `shiftL` i)
    , Property "maxBound value" $ \(a :: a) ->
        case bitSizeMaybe a of
          Just bs ->
            let actualMaxBound :: a
                actualMaxBound = maxBound
                expectedMaxBound :: Integer
                expectedMaxBound = 2^(cast bs :: Word) - (1 :: Integer)
            in toInteger actualMaxBound === expectedMaxBound
          Nothing -> propertyFail "Expected FiniteBits"
    , Property "complement maxBound" $
        complement 0 === (maxBound :: a)
    , Property "overflow maxBound" $
        maxBound + 1 === (0 :: a)
    , Property "underflow zero" $
        (0 :: a) - 1 === maxBound
    ]
  where
    convertBack x
        | x <= 0    = 0
        | otherwise = fromInteger x

tests = Group "Bits"
{-
    [ Property "round-up" $ \(Positive m) n' -> n' >= 1 ==>
        let n = 2 ^ ((n' `mod` 30) :: Word)
            md = alignRoundUp m n
         in (md `mod` n) == 0 && md >= m
         -}
    [ testBits "W32" (Proxy :: Proxy Word32) arbitrary
    , testBits "W64" (Proxy :: Proxy Word64) arbitrary
    , testBits "W128" (Proxy :: Proxy Word128) arbitrary
    , testBits "W256" (Proxy :: Proxy Word256) arbitrary
    ]
