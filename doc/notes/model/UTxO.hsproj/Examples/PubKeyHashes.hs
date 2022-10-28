{-# LANGUAGE PackageImports  #-}
{-# LANGUAGE TemplateHaskell #-}

module Examples.PubKeyHashes
where

import "cryptonite" Crypto.PubKey.ECC.ECDSA
import Crypto.PubKey.ECC.Generate
import Crypto.PubKey.ECC.Types
import "cryptonite" Crypto.Random

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Examples.Keys
import Ledger
import UTxO
import Witness


-- Template Haskell splices can't use local definitions, but only imported ones (stage restriction);
-- hence, we have got some defintions here that we want to use in 'Examples.PubKey'.
-- This is very sad!

t1Hash = hashTx $
           Tx []
              [TxOut val1Hash 1000] 1000 0
  where
    val1Hash = scriptHash $$(lockWithPublicKeyValidator (toPublicKey myKeyPair1))

wit2Hash = validatorHash $$(revealPreimage "2")

val1Hash = scriptHash $$(lockWithPublicKeyValidator (toPublicKey myKeyPair1))
