{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Functions for working with the contract interface using typed transactions.
module Language.Plutus.Contract.Typed.Tx where

import           Ledger.Constraints               (TxConstraints)
import           Ledger.Constraints.TxConstraints (addTxIn)

import           Data.Foldable                    (foldl')
import qualified Data.Map                         as Map

import           Ledger                           (TxOutRef, TxOutTx)

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that match a predicate, using the 'RedeemerValue'.
collectFromScriptFilter ::
    forall i o
    .  (TxOutRef -> TxOutTx -> Bool)
    -> Map.Map TxOutRef TxOutTx
    -> i
    -> TxConstraints i o
collectFromScriptFilter flt utxo red =
    let ourUtxo :: Map.Map TxOutRef TxOutTx
        ourUtxo = Map.filterWithKey flt utxo
    in collectFromScript ourUtxo red

-- | A version of 'collectFromScript' that selects all outputs
--   at the address
collectFromScript ::
    forall i o
    .  Map.Map TxOutRef TxOutTx
    -> i
    -> TxConstraints i o
collectFromScript utxo redeemer =
    foldl' (\b a -> addTxIn a redeemer b) mempty (Map.keys utxo)
