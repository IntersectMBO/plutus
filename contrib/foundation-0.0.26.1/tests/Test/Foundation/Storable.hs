{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Test.Foundation.Storable
    ( testForeignStorableRefs
    , testPropertyStorable, testPropertyStorableFixed
    ) where

import Foundation
import Foundation.Class.Storable
import Foundation.Primitive
import Foundation.Check

import qualified Foreign.Storable
import qualified Foreign.Marshal.Alloc
import qualified Foreign.Marshal.Array

testForeignStorableRefs :: Test
testForeignStorableRefs = Group "Storable"
    [ Group "Storable"
        [ testPropertyStorable "Word8" (Proxy :: Proxy Word8)
        , testPropertyStorable "Word16" (Proxy :: Proxy Word16)
        , testPropertyStorable "Word32" (Proxy :: Proxy Word32)
        , testPropertyStorable "Word64" (Proxy :: Proxy Word64)
        , testPropertyStorable "Int8" (Proxy :: Proxy Int8)
        , testPropertyStorable "Int16" (Proxy :: Proxy Int16)
        , testPropertyStorable "Int32" (Proxy :: Proxy Int32)
        , testPropertyStorable "Int64" (Proxy :: Proxy Int64)
        , testPropertyStorable "Char" (Proxy :: Proxy Char)
        , testPropertyStorable "Double" (Proxy :: Proxy Double)
        , testPropertyStorable "Float" (Proxy :: Proxy Float)
        ]
    , Group "StorableFixed"
        [ testPropertyStorableFixed "Word8" (Proxy :: Proxy Word8)
        , testPropertyStorableFixed "Word16" (Proxy :: Proxy Word16)
        , testPropertyStorableFixed "Word32" (Proxy :: Proxy Word32)
        , testPropertyStorableFixed "Word64" (Proxy :: Proxy Word64)
        , testPropertyStorableFixed "Int8" (Proxy :: Proxy Int8)
        , testPropertyStorableFixed "Int16" (Proxy :: Proxy Int16)
        , testPropertyStorableFixed "Int32" (Proxy :: Proxy Int32)
        , testPropertyStorableFixed "Int64" (Proxy :: Proxy Int64)
        , testPropertyStorableFixed "Char" (Proxy :: Proxy Char)
        , testPropertyStorableFixed "Double" (Proxy :: Proxy Double)
        , testPropertyStorableFixed "Float" (Proxy :: Proxy Float)
        ]
    , Group "Endianness"
        [ testPropertyBE "Word16" (Proxy :: Proxy Word16)
        , testPropertyBE "Word32" (Proxy :: Proxy Word32)
        , testPropertyBE "Word64" (Proxy :: Proxy Word64)
        ]
    ]

testPropertyBE :: forall a . (ByteSwap a, StorableFixed a, Arbitrary a, Eq a, Show a, Typeable a)
               => String
               -> Proxy a
               -> Test
testPropertyBE name p = Group name
    [ Property "fromBE . toBE == id" $ \(a :: a) -> fromBE (toBE a) === a
    , Property "fromLE . toLE == id" $ \(a :: a) -> fromLE (toLE a) === a
    ]

testPropertyStorable :: (Storable a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                     => String
                     -> Proxy a
                     -> Test
testPropertyStorable name p = Group name
    [ -- testPropertyStorablePeek p
    -- , testPropertyStorablePoke p
    ]

testPropertyStorableFixed :: forall a . (StorableFixed a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                          => String
                          -> Proxy a
                          -> Test
testPropertyStorableFixed name p = Group name
    [ Property "size"      $ \(a :: a) -> size p === (CountOf $ Foreign.Storable.sizeOf a)
    , Property "alignment" $ \(a :: a) -> alignment p === (CountOf $ Foreign.Storable.alignment a)
    --, testPropertyStorableFixedPeekOff p
    --, testPropertyStorableFixedPokeOff p
    ]

testPropertyStorablePeek :: (Storable a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                         => Proxy a
                         -> a
                         -> Test
testPropertyStorablePeek _ v = CheckPlan "storable-peek" $ do
    v' <- pick "alloca" $ Foreign.Marshal.Alloc.alloca $ \ptr -> do
            Foreign.Storable.poke ptr v
            peek ptr
    validate "equal" $ v == v'

testPropertyStorablePoke :: (Storable a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                         => Proxy a
                         -> a
                         -> Test
testPropertyStorablePoke _ v = CheckPlan "storable-poke" $ do
    v' <- pick "alloca" $ Foreign.Marshal.Alloc.alloca $ \ptr -> do
            poke ptr v
            Foreign.Storable.peek ptr
    validate "equal" $ v == v'

{-
assertEq a b
  | a == b = assert True
  | otherwise = do
      run $ putStrLn $ show a <> " /= " <> show b
      assert False
      -}

data SomeWhereInArray a = SomeWhereInArray a Int Int
    deriving (Show, Eq)
instance (StorableFixed a, Arbitrary a) => Arbitrary (SomeWhereInArray a) where
    arbitrary = do
        a  <- arbitrary
        let p = Proxy :: Proxy a
            Just (CountOf minsz) = (size p + alignment p - size p)
        let sz = minsz + 1
        let o = sz - minsz
        --sz <- choose (minsz, 512)
        --o  <- choose (0, sz - minsz)
        return $ SomeWhereInArray a sz o

{-
testPropertyStorableFixedPeekOff :: (StorableFixed a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                         => Proxy a
                         -> SomeWhereInArray a
                         -> Test
testPropertyStorableFixedPeekOff = CheckPlan "storable-fixed-peek-off" $ do
    (SomeWhereInArray v sz off) <- pick "x" arbitrary
    v' <- pick "alloca" $ Foreign.Marshal.Array.allocaArray sz $ \ptr -> do
            Foreign.Storable.pokeElemOff ptr off v
            peekOff ptr (Offset off)
    validate "equal" $ v == v'

testPropertyStorableFixedPokeOff :: (StorableFixed a, Foreign.Storable.Storable a, Arbitrary a, Eq a, Show a)
                         => Proxy a
                         -> SomeWhereInArray a
                         -> Test
testPropertyStorableFixedPokeOff _ (SomeWhereInArray v sz off) = CheckPlan "storable-fixed-poke-off" $ do
    v' <- pick "alloca" $ Foreign.Marshal.Array.allocaArray sz $ \ptr -> do
            pokeOff ptr (Offset off) v
            Foreign.Storable.peekElemOff ptr off
    validate "equal" $ v == v'
    -}
