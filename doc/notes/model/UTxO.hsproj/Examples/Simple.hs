{-# LANGUAGE TemplateHaskell #-}

module Examples.Simple
where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Ledger
import UTxO
import Witness


simpleLedger = [t6, t5, t4, t3, t2, t1]
  where
    t1 = Tx []
            [TxOut (vhash wit1) 1000] 1000 0
    t2 = Tx [txIn (hashTx t1) 0 wit1]
            [TxOut (vhash wit2) 800, TxOut (vhash wit1) 200] 0 0
    t3 = Tx [txIn (hashTx t2) 1 wit1]
            [TxOut (vhash wit3) 199] 0 1
    t4 = Tx [txIn (hashTx t3) 0 wit3]
            [TxOut (vhash wit2) 207] 10 2
    t5 = Tx [txIn (hashTx t4) 0 wit2, txIn (hashTx t2) 0 wit2]
            [TxOut (vhash wit2) 500, TxOut (vhash wit3) 500] 0 7
    t6 = Tx [txIn (hashTx t5) 0 wit2, txIn (hashTx t5) 1 wit3]
            [TxOut (vhash wit3) 999] 0 1

    vhash = validatorHash
    wit1  = $(revealPreimage "1")
    wit2  = $(revealPreimage "2")
    wit3  = $(revealPreimage "3")

failingLedger = [t2, t1]
  where
    t1 = Tx []
            [TxOut (vhash wit1) 1000] 1000 0
    t2 = Tx [txIn (hashTx t1) 0 wit1]
            [TxOut (vhash wit2) 800, TxOut (vhash wit1) 200] 0 0

    vhash = validatorHash
    wit1  = $(witness (revealPreimageValidator "1") (script [|| const "wrong" ||]))
    wit2  = $(revealPreimage "2")
