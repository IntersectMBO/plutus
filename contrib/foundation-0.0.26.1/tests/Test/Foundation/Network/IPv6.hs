{-# LANGUAGE CPP               #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module Test.Foundation.Network.IPv6
    ( testNetworkIPv6
    ) where

import Foundation
import Foundation.Check
import Foundation.Network.IPv6

import Test.Data.Network
import Test.Foundation.Storable

-- | test property equality for the given Collection
testEquality :: Gen IPv6 -> Test
testEquality genElement = Group "equality"
    [ Property "x == x" $ forAll genElement (\x -> x === x)
    , Property "x == y" $ forAll ((,) <$> genElement <*> genElement) $
        \(x,y) -> (toTuple x == toTuple y) === (x == y)
    ]

-- | test ordering
testOrdering :: Gen IPv6 -> Test
testOrdering genElement = Property "ordering" $
    forAll ((,) <$> genElement <*> genElement) $ \(x, y) ->
        (toTuple x `compare` toTuple y) === x `compare` y

testNetworkIPv6 :: Test
testNetworkIPv6 = Group "IPv6"
#if __GLASGOW_HASKELL__ >= 710
    [ Property "toTuple . fromTuple == id" $
        forAll genIPv6Tuple $ \x -> x === toTuple (fromTuple x)
    , Property "toString . fromString == id" $
        forAll genIPv6String $ \x -> x === toString (fromString $ toList x)
    , testEquality genIPv6
    , testOrdering genIPv6
    , testPropertyStorable      "Storable" (Proxy :: Proxy IPv6)
    , testPropertyStorableFixed "StorableFixed" (Proxy :: Proxy IPv6)
    , Group "parse"
        [ Property "::"  $ fromTuple (0,0,0,0,0,0,0,0) === fromString "::"
        , Property "::1" $ fromTuple (0,0,0,0,0,0,0,1) === fromString "::1"
        , Property "2001:DB8::8:800:200C:417A" $ fromTuple (0x2001,0xDB8,0,0,0x8,0x800,0x200c,0x417a) === fromString "2001:DB8::8:800:200C:417A"
        , Property "FF01::101" $ fromTuple (0xff01,0,0,0,0,0,0,0x101) === fromString "FF01::101"
        , Property "::13.1.68.3" $ (fromTuple (0,0,0,0,0,0,0x0d01,0x4403)) === (fromString "::13.1.68.3")
        , Property "::FFFF:129.144.52.38" $ (fromTuple (0,0,0,0,0,0xffff,0x8190,0x3426)) === (fromString "::FFFF:129.144.52.38")
        , Property "0::FFFF:129.144.52.38" $ (fromTuple (0,0,0,0,0,0xffff,0x8190,0x3426)) === (fromString "0::FFFF:129.144.52.38")
        , Property "0:0::FFFF:129.144.52.38" $ (fromTuple (0,0,0,0,0,0xffff,0x8190,0x3426)) === (fromString "0:0::FFFF:129.144.52.38")
        ]
    ]
#else
    []
#endif
