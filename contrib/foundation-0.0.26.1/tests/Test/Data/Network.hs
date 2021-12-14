-- |
-- Module:
-- Author: Nicolas Di Prima <nicolas>
-- Date:   2017-01-18T17:34:06+00:00
-- Email:  nicolasdiprima@gmail.com
--

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module Test.Data.Network
    ( genIPv4
    , genIPv4Tuple
    , genIPv4String
    , genIPv6
    , genIPv6Tuple
    , genIPv6String
    ) where

import Foundation
import Foundation.Check
import Foundation.Network.IPv4 as IPv4
import Foundation.Network.IPv6 as IPv6
import Foundation.Class.Storable as F
import qualified Foreign.Storable as Foreign

instance Arbitrary IPv4 where
    arbitrary = genIPv4
instance Foreign.Storable IPv4 where
    sizeOf a = let CountOf b = F.size (Just a) in b
    alignment a = let CountOf b = F.alignment (Just a) in b
    peek = F.peek
    poke = F.poke
instance Arbitrary IPv6 where
    arbitrary = genIPv6
instance Foreign.Storable IPv6 where
    sizeOf a = let CountOf b = F.size (Just a) in b
    alignment a = let CountOf b = F.alignment (Just a) in b
    peek = F.peek
    poke = F.poke

genIPv4Tuple :: Gen (Word8, Word8, Word8, Word8)
genIPv4Tuple =
    (,,,) <$> arbitrary
          <*> arbitrary
          <*> arbitrary
          <*> arbitrary

genIPv6Tuple :: Gen (Word16, Word16, Word16, Word16, Word16, Word16, Word16, Word16)
genIPv6Tuple =
    (,,,,,,,) <$> arbitrary
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary
              <*> arbitrary

genIPv4String :: Gen String
genIPv4String = do
    (w1, w2, w3, w4) <- genIPv4Tuple
    return $ show w1 <> "." <> show w2 <> "." <> show w3 <> "." <> show w4

genIPv6String :: Gen String
genIPv6String = IPv6.toString <$> genIPv6

genIPv6 :: Gen IPv6
genIPv6 = IPv6.fromTuple <$> genIPv6Tuple

-- | a better generator for unicode Character
genIPv4 :: Gen IPv4
genIPv4 = IPv4.fromTuple <$> genIPv4Tuple
