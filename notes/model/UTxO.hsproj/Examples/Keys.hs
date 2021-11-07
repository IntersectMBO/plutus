{-# LANGUAGE PackageImports  #-}
{-# LANGUAGE TemplateHaskell #-}

module Examples.Keys
where

import "cryptonite" Crypto.PubKey.ECC.ECDSA
import Crypto.PubKey.ECC.Generate
import Crypto.PubKey.ECC.Types
import "cryptonite" Crypto.Random

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set


myKeyPair1 :: KeyPair
myKeyPair1 = KeyPair (private_curve . snd $ keys) (public_q . fst $ keys) (private_d . snd $ keys)
  where
    curve     = getCurveByName SEC_p112r1
    drg       = drgNewSeed (seedFromInteger 42)
    (keys, _) = withDRG drg $
                  generate curve
