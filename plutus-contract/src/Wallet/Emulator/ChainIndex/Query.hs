{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
module Wallet.Emulator.ChainIndex.Query where

import           Control.Monad.Freer.TH (makeEffect)
import qualified Data.ByteString        as BS
import           Data.Set               (Set)
import           Ledger                 (Datum, DatumHash, MonetaryPolicy, MonetaryPolicyHash, Slot, Validator,
                                         ValidatorHash)
import           Ledger.Tx              (TxOut, TxOutRef)

newtype BlockId = BlockId { getBlockId :: BS.ByteString }
    deriving (Eq, Ord)

data ChainIndexQueryEffect r where
    DatumFromHash :: DatumHash -> ChainIndexQueryEffect (Maybe Datum)
    ValidatorFromHash :: ValidatorHash -> ChainIndexQueryEffect (Maybe Validator)
    MonetaryPolicyFromHash :: MonetaryPolicyHash -> ChainIndexQueryEffect (Maybe MonetaryPolicy)
    TxOutFromRef :: TxOutRef -> ChainIndexQueryEffect (Maybe TxOut)
    UtxoSet :: ChainIndexQueryEffect (Set TxOutRef)
    Tip :: ChainIndexQueryEffect (Slot, Maybe BlockId)

makeEffect ''ChainIndexQueryEffect
