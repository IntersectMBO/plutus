{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE CPP #-}
module Main where


import Foundation
import Foundation.Array
import Foundation.Foreign
import Foundation.List.DList
import Foundation.Primitive
import Foundation.Check
import Foundation.Check.Main (defaultMain)
import Foundation.String
import Foundation.String.Read
import qualified Prelude
import Data.Ratio

import Test.Foundation.Random
import Test.Foundation.Misc
import Test.Foundation.Storable
import Test.Foundation.Number
import Test.Foundation.Conduit
import Test.Foundation.String
import Test.Foundation.Network.IPv4
import Test.Foundation.Network.IPv6
import Test.Foundation.String.Base64
import Test.Checks.Property.Collection
import Test.Foundation.Format
import qualified Test.Foundation.Bits as Bits
import qualified Test.Basement as Basement

#if MIN_VERSION_base(4,9,0)
import Test.Foundation.Primitive.BlockN
#endif

applyFstToSnd :: (String, String -> b) -> b
applyFstToSnd (a, fab) = fab a

matrixToGroup name l = Group name $ Prelude.concat $ fmap (fmap applyFstToSnd . snd) l

functorProxy :: Proxy f -> Proxy ty -> Proxy (f ty)
functorProxy _ _ = Proxy

primTypesMatrixArbitrary :: (forall ty . (PrimType ty, Typeable ty, Show ty, Ord ty) => Proxy ty -> Gen ty -> a)
                         -> [(String, [(String, a)])]
primTypesMatrixArbitrary f =
    [ ("Words",
        [ ("W8", f (Proxy :: Proxy Word8) arbitrary)
        , ("W16", f (Proxy :: Proxy Word16) arbitrary)
        , ("W32", f (Proxy :: Proxy Word32) arbitrary)
        , ("W64", f (Proxy :: Proxy Word64) arbitrary)
        , ("W128", f (Proxy :: Proxy Word128) arbitrary)
        , ("W256", f (Proxy :: Proxy Word256) arbitrary)
        , ("Word", f (Proxy :: Proxy Word) arbitrary)
        ])
    , ("Ints",
        [ ("I8", f (Proxy :: Proxy Int8) arbitrary)
        , ("I16", f (Proxy :: Proxy Int16) arbitrary)
        , ("I32", f (Proxy :: Proxy Int32) arbitrary)
        , ("I64", f (Proxy :: Proxy Int64) arbitrary)
        , ("Int", f (Proxy :: Proxy Int) arbitrary)
        ])
    , ("Floating",
        [ ("FP32", f (Proxy :: Proxy Float) arbitrary)
        , ("FP64", f (Proxy :: Proxy Double) arbitrary)
        ])
    , ("C-Types",
        [ ("CChar", f (Proxy :: Proxy CChar) (CChar <$> arbitrary))
        , ("CUChar", f (Proxy :: Proxy CUChar) (CUChar <$> arbitrary))
        ])
    , ("Endian",
        [ ("BE-W16", f (Proxy :: Proxy (BE Word16)) (toBE <$> arbitrary))
        , ("BE-W32", f (Proxy :: Proxy (BE Word32)) (toBE <$> arbitrary))
        , ("BE-W64", f (Proxy :: Proxy (BE Word64)) (toBE <$> arbitrary))
        , ("LE-W16", f (Proxy :: Proxy (LE Word16)) (toLE <$> arbitrary))
        , ("LE-W32", f (Proxy :: Proxy (LE Word32)) (toLE <$> arbitrary))
        , ("LE-W64", f (Proxy :: Proxy (LE Word64)) (toLE <$> arbitrary))
        ])
    ]

testAdditive :: forall a . (Show a, Eq a, Typeable a, Additive a, Arbitrary a) => Proxy a -> Test
testAdditive _ = Group "Additive"
    [ Property "eq"             $ azero === (azero :: a)
    , Property "a + azero == a" $ \(v :: a)     -> v + azero === v
    , Property "azero + a == a" $ \(v :: a)     -> azero + v === v
    , Property "a + b == b + a" $ \(v1 :: a) v2 -> v1 + v2 === v2 + v1
    ]

readFloatingExact' :: String -> Maybe (Bool, Natural, Word, Maybe Int)
readFloatingExact' str = readFloatingExact str (\s x y z -> Just (s,x,y,z))

doubleEqualApprox :: Double -> Double -> PropertyCheck
doubleEqualApprox d1 d2 = propertyCompare name (<) (abs d) lim
  where
        d = d2 - d1

        name = show d1 <> " - " <> show d2 <> " (differential=" <> show (abs d) <> " )" <> " < " <> show lim

        lim = min d1 d2 * (10^^(-15 :: Int))

main = defaultMain $ Group "foundation"
    [ Group "Numerical"
        [ Group "Int"
            [ testAdditive (Proxy :: Proxy Int)
            ]
        , Group "Word64"
            [ testAdditive (Proxy :: Proxy Word64)
            ]
        , Group "Number" testNumberRefs
        ]
    , Basement.tests
    , Bits.tests
    , Group "String"
        [ Group "reading"
            [ Group "integer"
                [ Property "empty"         $ readInteger "" === Nothing
                , Property "just-sign"     $ readInteger "-" === Nothing
                , Property "extra-content" $ readInteger "-123a" === Nothing
                , Property "any"           $ \i -> readInteger (show i) === Just i
                ]
            , Group "floating-exact"
                [ Property "empty"         $ readFloatingExact' "" === Nothing
                , Property "just-sign"     $ readFloatingExact' "-" === Nothing
                , Property "extra-content" $ readFloatingExact' "-123a" === Nothing
                , Property "no-dot-after"  $ readFloatingExact' "-123." === Nothing
                , Property "case0"         $ readFloatingExact' "124890" === Just (False, 124890, 0, Nothing)
                , Property "case1"         $ readFloatingExact' "-123.1" === Just (True, 1231, 1, Nothing)
                , Property "case2"         $ readFloatingExact' "10001.001" === Just (False, 10001001, 3, Nothing)
{-
                , Property "any"           $ \s i (v :: Word8) n ->
                                                let (integral,floating) = i `divMod` (10^v)
                                                let vw = integralUpsize v :: Word
                                                    sfloat = show n
                                                    digits = integralCast (length sfloat) + vw
                                                 in readFloatingExact' ((if s then "-" else "") <> show i <> "." <> replicate vw '0' <> sfloat) === Just (s, i, Just (digits, n), Nothing)
-}
                ]
            , Group "Double"
                [ Property "case1" $ readDouble "96152.5" === Just 96152.5
                , Property "case2" $ maybe (propertyFail "Nothing") (doubleEqualApprox 1.2300000000000002e102) $ readDouble "1.2300000000000002e102"
                , Property "case3" $ maybe (propertyFail "Nothing") (doubleEqualApprox 0.00001204) $ readDouble "0.00001204"
                , Property "case4" $ maybe (propertyFail "Nothing") (doubleEqualApprox 2.5e12) $ readDouble "2.5e12"
                , Property "case5" $ maybe (propertyFail "Nothing") (doubleEqualApprox 6.0e-4) $ readDouble "6.0e-4"
                , Property "case6" $ maybe (propertyFail "Nothing") ((===) (-31.548)) $ readDouble "-31.548"
                , Property "case7" $ readDouble "1e100000000" === Just (1/0)
                , Property "Prelude.read" $ \(d :: Double) -> case readDouble (show d) of
                                                                  Nothing -> propertyFail "Nothing"
                                                                  Just d' -> d' `doubleEqualApprox` (Prelude.read $ toList $ show d)
                ]
            , Group "rational"
                [ Property "case1" $ readRational "124.098" === Just (124098 % 1000)
                ]
            ]
        , Group "conversion"
            [ Property "lower" $ lower "This is MY test" === "this is my test"
            , Property "upper" $ upper "This is MY test" === "THIS IS MY TEST"
            ]
        ]
    , collectionProperties "DList a" (Proxy :: Proxy (DList Word8)) arbitrary
    , collectionProperties "Bitmap"  (Proxy :: Proxy Bitmap)  arbitrary
    , Group "Array"
      [ matrixToGroup "Block" $ primTypesMatrixArbitrary $ \prx arb s ->
            collectionProperties ("Block " <> s) (functorProxy (Proxy :: Proxy Block) prx) arb
      , matrixToGroup "Unboxed" $ primTypesMatrixArbitrary $ \prx arb s ->
            collectionProperties ("Unboxed " <> s) (functorProxy (Proxy :: Proxy UArray) prx) arb
      , Group "Boxed"
        [ collectionProperties "Array(W8)"  (Proxy :: Proxy (Array Word8))  arbitrary
        , collectionProperties "Array(W16)" (Proxy :: Proxy (Array Word16)) arbitrary
        , collectionProperties "Array(W32)" (Proxy :: Proxy (Array Word32)) arbitrary
        , collectionProperties "Array(W64)" (Proxy :: Proxy (Array Word64)) arbitrary
        , collectionProperties "Array(I8)"  (Proxy :: Proxy (Array Int8))   arbitrary
        , collectionProperties "Array(I16)" (Proxy :: Proxy (Array Int16))  arbitrary
        , collectionProperties "Array(I32)" (Proxy :: Proxy (Array Int32))  arbitrary
        , collectionProperties "Array(I64)" (Proxy :: Proxy (Array Int64))  arbitrary
        , collectionProperties "Array(F32)" (Proxy :: Proxy (Array Float))  arbitrary
        , collectionProperties "Array(F64)" (Proxy :: Proxy (Array Double)) arbitrary
        , collectionProperties "Array(Int)" (Proxy :: Proxy (Array Int))  arbitrary
        , collectionProperties "Array(Int,Int)" (Proxy :: Proxy (Array (Int,Int)))  arbitrary
        , collectionProperties "Array(Integer)" (Proxy :: Proxy (Array Integer)) arbitrary
        , collectionProperties "Array(CChar)"   (Proxy :: Proxy (Array CChar))  (CChar <$> arbitrary)
        , collectionProperties "Array(CUChar)"  (Proxy :: Proxy (Array CUChar)) (CUChar <$> arbitrary)
        , collectionProperties "Array(BE W16)"  (Proxy :: Proxy (Array (BE Word16))) (toBE <$> arbitrary)
        , collectionProperties "Array(BE W32)"  (Proxy :: Proxy (Array (BE Word32))) (toBE <$> arbitrary)
        , collectionProperties "Array(BE W64)"  (Proxy :: Proxy (Array (BE Word64))) (toBE <$> arbitrary)
        , collectionProperties "Array(LE W16)"  (Proxy :: Proxy (Array (LE Word16))) (toLE <$> arbitrary)
        , collectionProperties "Array(LE W32)"  (Proxy :: Proxy (Array (LE Word32))) (toLE <$> arbitrary)
        , collectionProperties "Array(LE W64)"  (Proxy :: Proxy (Array (LE Word64))) (toLE <$> arbitrary)
        ]
      ]
    , Group "ChunkedUArray"
      [ matrixToGroup "Unboxed" $ primTypesMatrixArbitrary $ \prx arb s ->
            collectionProperties ("Unboxed " <> s) (functorProxy (Proxy :: Proxy ChunkedUArray) prx) arb
      ]
    , testStringRefs
    , testForeignStorableRefs
    , testNetworkIPv4
    , testNetworkIPv6
    , testBase64Refs
    , testHexadecimal
    , testUUID
    , testRandom
    , testConduit
#if MIN_VERSION_base(4,9,0)
    , testBlockN
#endif
    , testFormat
    ]
