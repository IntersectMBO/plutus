{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE CPP #-}
module Test.Foundation.Number
    ( testNumber
    , testNumberRefs
    ) where

import Foundation
import Foundation.Check
import qualified Prelude

testIntegral :: forall a . (Arbitrary a, Show a, IsIntegral a, Integral a, Typeable a)
             => Proxy a -> Test
testIntegral _ = Group "Integral"
    [ Property "FromIntegral(Integer(a)) == a" $ \(a :: a) -> fromInteger (toInteger a) === a
    ]

testEqOrd :: forall a . (Arbitrary a, Show a, Eq a, Ord a, IsIntegral a, Typeable a)
          => Proxy a -> Test
testEqOrd _ = Group "Property"
    [ Property "Eq" $ \(a :: a) -> a === a
    -- , Property "Ne" $ \(a :: a) (b :: a) -> if a === w
    , Property "Show" $ \(a :: a) -> show a === show (toInteger a)
    , Property "Ord" $ \(a :: a) (b :: a) -> compare a b === (compare `on` toInteger) a b
    , Property "<" $ \(a :: a) (b :: a) -> case compare a b of
                                                LT -> propertyCompare "<" (<) a b
                                                GT -> propertyCompare "<" (<) b a
                                                EQ -> propertyCompare "not <" ((not .) . (<)) a b `propertyAnd`
                                                      propertyCompare "not <" ((not .) . (<)) b a
    ]

testAdditive :: forall a . (Show a, Eq a, Additive a, Arbitrary a, Typeable a)
             => Proxy a -> Test
testAdditive _ = Group "Additive"
    [ Property "a + azero == a" $ \(a :: a) -> a + azero === a
    , Property "azero + a == a" $ \(a :: a) -> azero + a === a
    , Property "a + b == b + a" $ \(a :: a) (b :: a) -> a + b === b + a
    ]

testMultiplicative :: forall a . (Show a, Eq a, IsIntegral a, Integral a, Multiplicative a, Arbitrary a, Typeable a)
                   => Proxy a -> Test
testMultiplicative _ = Group "Multiplicative"
    [ Property "a * 1 == a" $ \(a :: a) -> a * midentity === a
    , Property "1 * a == a" $ \(a :: a) -> midentity * a === a
    , Property "multiplication commutative" $ \(a :: a) (b :: a) -> a * b == b * a
    , Property "a * b == Integer(a) * Integer(b)" $ \(a :: a) (b :: a) -> a * b == fromInteger (toInteger a * toInteger b)
    ]

testDividible :: forall a . (Show a, Eq a, IsIntegral a, IDivisible a, Arbitrary a, Typeable a)
              => Proxy a -> Test
testDividible _ = Group "Divisible"
    [ Property "(x `div` y) * y + (x `mod` y) == x" $ \(a :: a) b ->
            if b == 0 then True === True
                      else a === (a `div` b) * b + (a `mod` b)
    ]

testOperatorPrecedence :: forall a . (Show a, Eq a, Prelude.Num a, IsIntegral a, Additive a, Subtractive a, Multiplicative a, Difference a ~ a, Arbitrary a, Typeable a)
                       => Proxy a -> Test
testOperatorPrecedence _ = Group "Precedence"
    [ Property "+ and - (1)" $ \(a :: a) (b :: a) (c :: a) -> (a + b - c) === ((a + b) - c)
    , Property "+ and - (2)" $ \(a :: a) (b :: a) (c :: a) -> (a - b + c) === ((a - b) + c)
    , Property "+ and * (1)" $ \(a :: a) (b :: a) (c :: a) -> (a + b * c) === (a + (b * c))
    , Property "+ and * (2)" $ \(a :: a) (b :: a) (c :: a) -> (a * b + c) === ((a * b) + c)
    , Property "- and * (1)" $ \(a :: a) (b :: a) (c :: a) -> (a - b * c) === (a - (b * c))
    , Property "- and * (2)" $ \(a :: a) (b :: a) (c :: a) -> (a * b - c) === ((a * b) - c)
    , Property "* and ^ (1)" $ \(a :: a) (b :: Natural) (c :: a) -> (a ^ b * c) === ((a ^ b) * c)
    , Property "* and ^ (2)" $ \(a :: a) (c :: Natural) (b :: a) -> (a * b ^ c) === (a * (b ^ c))
    ]


testNumber :: (Show a, Eq a, Prelude.Num a, IsIntegral a, Additive a, Multiplicative a, Subtractive a, Difference a ~ a, IDivisible a, Arbitrary a, Typeable a)
           => String -> Proxy a -> Test
testNumber name proxy = Group name
    [ testIntegral proxy
    , testEqOrd proxy
    , testAdditive proxy
    , testMultiplicative proxy
    , testDividible proxy
    , testOperatorPrecedence proxy
    ]

testNumberRefs :: [Test]
testNumberRefs =
    [ testNumber "Int" (Proxy :: Proxy Int)
    , testNumber "Int8" (Proxy :: Proxy Int8)
    , testNumber "Int16" (Proxy :: Proxy Int16)
    , testNumber "Int32" (Proxy :: Proxy Int32)
    , testNumber "Int64" (Proxy :: Proxy Int64)
    , testNumber "Integer" (Proxy :: Proxy Integer)
    , testNumber "Word" (Proxy :: Proxy Word)
    , testNumber "Word8" (Proxy :: Proxy Word8)
    , testNumber "Word16" (Proxy :: Proxy Word16)
    , testNumber "Word32" (Proxy :: Proxy Word32)
    , testNumber "Word64" (Proxy :: Proxy Word64)
    , testNumber "Word128" (Proxy :: Proxy Word128)
    , testNumber "Word256" (Proxy :: Proxy Word256)
    ]
