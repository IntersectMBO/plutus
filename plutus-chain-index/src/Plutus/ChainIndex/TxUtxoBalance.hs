{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Plutus.ChainIndex.TxUtxoBalance where

import           Control.Lens                (view)
import           Data.Set                    (Set)
import qualified Data.Set                    as Set
import           Ledger                      (TxIn (txInRef), TxOutRef (..))
import           Plutus.ChainIndex.Tx        (ChainIndexTx (..), citxInputs, txOutsWithRef)
import           Plutus.ChainIndex.Types     (Point (..), Tip (..), TxUtxoBalance (..), tubUnspentOutputs)
import           Plutus.ChainIndex.UtxoState (RollbackFailed, RollbackResult, UtxoIndex,
                                              UtxoState (UtxoState, _usTip, _usTxUtxoData), rollbackWith, usTxUtxoData)

fromTx :: ChainIndexTx -> TxUtxoBalance
fromTx tx =
    TxUtxoBalance
        { _tubUnspentOutputs = Set.fromList $ fmap snd $ txOutsWithRef tx
        , _tubUnmatchedSpentInputs = Set.mapMonotonic txInRef (view citxInputs tx)
        }

-- | Whether a 'TxOutRef' is a member of the UTXO set (ie. unspent)
isUnspentOutput :: TxOutRef -> UtxoState TxUtxoBalance -> Bool
isUnspentOutput r = Set.member r . view (usTxUtxoData . tubUnspentOutputs)

-- | The UTXO set
unspentOutputs :: UtxoState TxUtxoBalance -> Set TxOutRef
unspentOutputs = view (usTxUtxoData . tubUnspentOutputs)

-- | 'UtxoIndex' for a single block
fromBlock :: Tip -> [ChainIndexTx] -> UtxoState TxUtxoBalance
fromBlock tip_ transactions =
    UtxoState
            { _usTxUtxoData = foldMap fromTx transactions
            , _usTip        = tip_
            }

-- | Perform a rollback on the utxo index
rollback :: Point
         -> UtxoIndex TxUtxoBalance
         -> Either RollbackFailed (RollbackResult TxUtxoBalance)
rollback = rollbackWith const
