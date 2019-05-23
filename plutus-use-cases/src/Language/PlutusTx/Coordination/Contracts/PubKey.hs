{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- | A "pay-to-pubkey" transaction output implemented as a Plutus
--   contract. This is useful if you need something that behaves like
--   a pay-to-pubkey output, but is not (easily) identified by wallets
--   as one.
module Language.PlutusTx.Coordination.Contracts.PubKey(lock) where

import           Data.Maybe (listToMaybe)
import qualified Data.Map   as Map
import qualified Data.Text  as Text

import qualified Language.PlutusTx            as P
import           Ledger                       as Ledger hiding (initialise, to)
import           Ledger.Validation            as V
import           Wallet.API                   as WAPI

mkValidator :: PubKey -> () -> () -> PendingTx -> Bool
mkValidator pk' () () p = V.txSignedBy p pk'

pkValidator :: PubKey -> ValidatorScript
pkValidator pk = ValidatorScript $
    Ledger.fromCompiledCode $$(P.compile [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted pk

-- | Lock some funds in a 'PayToPubKey' contract, returning the output's address
--   and a 'TxIn' transaction input that can spend it.
lock :: (WalletAPI m, WalletDiagnostics m) => PubKey -> Value -> m (Address, TxIn)
lock pk vl = getRef =<< payToScript defaultSlotRange addr vl pkDataScript where
    addr = Ledger.scriptAddress (pkValidator pk)
    pkDataScript = DataScript $ Ledger.lifted ()
    pkRedeemer = RedeemerScript $ Ledger.lifted ()

    getRef tx = do
        let scriptOuts = listToMaybe
                            $ fmap fst
                            $ filter ((==) addr . txOutAddress . snd)
                            $ Map.toList (unspentOutputsTx tx)

        txin <- case scriptOuts of
                    Nothing -> throwOtherError
                                $ "transaction did not contain script output"
                                <> "for public key '"
                                <> Text.pack (show pk)
                                <> "'"
                    Just o  -> pure (scriptTxIn o (pkValidator pk) pkRedeemer)

        pure (addr, txin)
