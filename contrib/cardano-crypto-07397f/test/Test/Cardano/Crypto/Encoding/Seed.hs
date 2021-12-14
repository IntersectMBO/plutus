{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Test.Cardano.Crypto.Encoding.Seed
    ( tests
    ) where

import Foundation
import Foundation.Check
import Foundation.String (words)
import Basement.Nat

import Crypto.Encoding.BIP39
import Crypto.Encoding.BIP39.English (english)

import Crypto.Error (throwCryptoError)

import Cardano.Crypto.Encoding.Seed as PW

-- -------------------------------------------------------------------------- --
--                            Encoding/Seed                                   --
-- -------------------------------------------------------------------------- --

tests :: Test
tests = Group "Seed (paper-wallet)"
    [ go (Proxy @128)
    , go (Proxy @160)
    , go (Proxy @192)
    ]
  where
    go :: forall n m s
        . ( PW.ConsistentEntropy n m s
          , PW.ConsistentEntropy (n + PW.IVSizeBits) (m + PW.IVSizeWords) (CheckSumBits (n + PW.IVSizeBits))
          , Arbitrary (PW.Entropy n)
          )
       => Proxy n
       -> Test
    go pr = Property ("unscramble . scramble @" <> sz <> " == id") $ \iv (e :: PW.Entropy n) p ->
        let s = PW.scramble @n iv e p
            u = PW.unscramble s p
         in e === u
      where
         sz = show $ natVal pr
