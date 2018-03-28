{-# LANGUAGE PackageImports, BangPatterns, TemplateHaskell #-}

-- This code models a UTxO-style ledger using the approach from
-- "An Abstract Model of UTXO-based Cryptocurrencies with Scripts"
-- using Template Haskell as a concrete notation for validation
-- scirpts.

-- |
-- Module      : UTxO
-- Copyright   : [2018] IOHK
-- License     : MIT
--
-- Maintainer  : Manuel M T Chakravarty <manuel.chakravarty@iohk.io>
-- Stability   : experimental
--
-- UTxO model definition

module UTxO 
where

import "cryptonite" 
       Crypto.Hash
import Data.List  
import Data.Set       (Set)
import qualified
       Data.Set       as Set
import Data.Map       (Map)
import qualified
       Data.Map       as Map
import Data.Maybe

import Ledger
import Types
import Witness


-- |Determine the transaction that an input refers to.
--
-- NB: Arguments swapped wrt to the paper.
--
tx :: Ledger -> TxOutRef -> Maybe Tx
tx ledger txOutRef
  = case [t | t <- ledger, hashTx t == idTOR txOutRef] of
      []     -> Nothing
      (t:_) -> Just t
  
-- |Determine the unspent output that an input refers to.
--
-- NB: Arguments swapped wrt to the paper.
--
out :: Ledger -> TxOutRef -> Maybe TxOut
out ledger txOutRef
  = do
    { t <- tx ledger txOutRef
    ; if length (outputsTX t) <= indexTOR txOutRef
        then fail ""
        else return $ outputsTX t !! indexTOR txOutRef
    }
  
-- |Determine the unspent value that an input refers to.
--  
-- NB: Arguments swapped wrt to the paper.
--
value :: Ledger -> TxOutRef -> Maybe Value
value ledger txOutRef
  = do
    { outTx <- out ledger txOutRef
    ; return $ valueTO outTx
    }
    
-- 

-- |The unspent outputs of a transaction.
--
-- Compared to the paper, we use a map and not a set. This saves expensive ledger
-- traversals in 'valid'.
--
unspentOutputsTx :: Tx -> Map TxOutRef Address
unspentOutputsTx tx 
  = Map.fromList $ 
      [ (TxOutRef{ idTOR = hashTx tx, indexTOR = ix }, addressTO txOut)
      | (txOut, ix) <- zip (outputsTX tx) [0..] 
      ]

-- |The outputs spent by a transaction (represented as inputs).
-- 
spentOutputsTx :: Tx -> Set TxOutRef
spentOutputsTx = Set.fromList . map refTI . inputsTX

--

-- |Unspent outputs of a ledger.
--
-- Compared to the paper, we use a map and not a set. This saves expensive ledger
-- traversals in 'valid'.
--
unspentOutputs :: Ledger -> Map TxOutRef Address
unspentOutputs 
  = foldr 
      (\t unspent -> (unspent `Map.difference` lift (spentOutputsTx t)) `Map.union` unspentOutputsTx t) 
      Map.empty
  where
    lift = Map.fromSet (const ())

-- |Determine whether a transaction is valid in a given ledger.
--
-- * The inputs refer to unspent outputs, which they unlock (input validity).
--
-- * The transaction preserves value (value preservation).
--
valid :: Tx -> Ledger -> Bool
valid t ledger = inputsAreValid && valueIsPreserved
  where
    inputsAreValid    = all (`validatesIn` unspentOutputs ledger) (inputsTX t)
    valueIsPreserved  = forgeTX t + sum (map (fromJust . value ledger) (map refTI $ inputsTX t))
                        == feeTX t + sum (map valueTO (outputsTX t))
                           -- NB: the 'fromMaybe' is safe as 'inputsAreUnspent' holds if we get here

    txIn `validatesIn` txOuts 
      = case refTI txIn `Map.lookup` txOuts of
          Just addr -> validate addr (state t ledger) (witnessTI txIn)
          _         -> False

-- |The UTxO balance of a given address in a valid transaction for the given ledger.
--
balanceTx :: Address -> Tx -> Ledger -> Value
balanceTx addr t ledger 
  | not (t `valid` ledger)
  = error "transaction not valid in ledger"
  | otherwise = received - spent
  where
    received = sum [ valueTO txOut | txOut <- outputsTX t, addressTO txOut == addr ]
    spent    = sum [ valueTO txOut 
                   | txOut <- catMaybes . map (out ledger . refTI) $ inputsTX t
                   , addressTO txOut == addr 
                   ]

-- |The UTxO balance of a given address in a ledger.
--
balance :: Address -> Ledger -> Value
balance addr = bal 0
  where
    bal !acc []     = acc
    bal !acc (t:ts) = bal (acc + balanceTx addr t ts) ts
