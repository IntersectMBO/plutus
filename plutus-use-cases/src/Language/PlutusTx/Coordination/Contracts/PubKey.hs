{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A "pay-to-pubkey" transaction output implemented as a Plutus
--   contract. This is useful if you need something that behaves like
--   a pay-to-pubkey output, but is not (easily) identified by wallets
--   as one.
module Language.PlutusTx.Coordination.Contracts.PubKey(pubKeyContract, scriptInstance) where

import           Control.Monad.Error.Lens (throwing)

import qualified Data.Map   as Map
import qualified Data.Text  as T

import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       as Ledger hiding (initialise, to)
import           Ledger.Typed.Scripts (ScriptInstance)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            as V

import           Language.Plutus.Contract     as Contract
import qualified Ledger.Constraints           as Constraints

mkValidator :: PubKeyHash -> () -> () -> PendingTx -> Bool
mkValidator pk' _ _ p = V.txSignedBy p pk'

data PubKeyContract

instance Scripts.ScriptType PubKeyContract where
    type instance DataType PubKeyContract = ()
    type instance RedeemerType PubKeyContract = ()

scriptInstance :: PubKeyHash -> Scripts.ScriptInstance PubKeyContract
scriptInstance pk =
    Scripts.validator @PubKeyContract
        ($$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode pk)
        $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @() @()

-- | Lock some funds in a 'PayToPubKey' contract, returning the output's address
--   and a 'TxIn' transaction input that can spend it.
pubKeyContract
    :: forall s e.
    ( HasWatchAddress s
    , HasWriteTx s
    , AsContractError e)
    => PubKeyHash
    -> Value
    -> Contract s e (TxOutRef, TxOutTx, ScriptInstance PubKeyContract)
pubKeyContract pk vl = do
    let inst = scriptInstance pk
        address = Scripts.scriptAddress inst
        tx = Constraints.mustPayToTheScript () vl
        
    tid <- submitTxConstraints inst tx

    ledgerTx <- awaitTransactionConfirmed address tid
    let output = Map.toList
                $ Map.filter ((==) address . txOutAddress)
                $ unspentOutputsTx ledgerTx
    case output of
        [] -> throwing _OtherError $
            "Transaction did not contain script output"
            <> "for public key '"
            <> T.pack (show pk)
            <> "'"
        [(outRef, outTxOut)] -> pure (outRef, TxOutTx{txOutTxTx = ledgerTx, txOutTxOut = outTxOut}, inst)
        _ -> throwing _OtherError $
            "Transaction contained multiple script outputs"
            <> "for public key '"
            <> T.pack (show pk)
            <> "'"
