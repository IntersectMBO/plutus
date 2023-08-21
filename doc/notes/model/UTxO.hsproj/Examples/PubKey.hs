{-# LANGUAGE PackageImports  #-}
{-# LANGUAGE TemplateHaskell #-}

module Examples.PubKey
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
import Examples.PubKeyHashes
import Ledger
import UTxO
import Witness


pubKeyLedger = [t2, t1]
  where
    t1 = Tx []
            [TxOut val1Hash 1000] 1000 0
    t2 = Tx [txIn (hashTx t1) 0 wit1]
            [TxOut (vhash wit2) 800, TxOut val1Hash 200] 0 0

    vhash    = validatorHash
    wit1     = $(lockWithKeyPair myKeyPair1
                    (preHashTx $ Tx [txIn t1Hash 0 noWitness] -- need a copy due to TH stage re
                                    [TxOut wit2Hash 800, TxOut val1Hash 200] 0 0))
    wit2     = $(revealPreimage "2")
