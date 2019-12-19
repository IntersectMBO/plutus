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
module Language.PlutusTx.Coordination.Contracts.PubKey(pubKeyContract) where

import           Control.Monad.Error.Lens (throwing)

import qualified Data.Map   as Map
import qualified Data.Text  as T

import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       as Ledger hiding (initialise, to)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            as V

import           Language.Plutus.Contract     as Contract

mkValidator :: PubKey -> () -> () -> PendingTx -> Bool
mkValidator pk' _ _ p = V.txSignedBy p pk'

pkValidator :: PubKey -> Validator
pkValidator pk = mkValidatorScript $
    $$(PlutusTx.compile [|| validatorParam ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode pk
    where validatorParam k = Scripts.wrapValidator (mkValidator k)

-- | Lock some funds in a 'PayToPubKey' contract, returning the output's address
--   and a 'TxIn' transaction input that can spend it.
pubKeyContract
    :: forall s e.
    ( HasWatchAddress s
    , HasWriteTx s
    , AsContractError e)
    => PubKey
    -> Value
    -> Contract s e TxIn
pubKeyContract pk vl = do
    let address = Ledger.scriptAddress (pkValidator pk)
        tx = Contract.payToScript vl address unitData
    tid <- submitTx tx

    ledgerTx <- awaitTransactionConfirmed address tid
    let output = Map.keys
                $ Map.filter ((==) address . txOutAddress)
                $ unspentOutputsTx ledgerTx
    ref <- case output of
        [] -> throwing _OtherError $
            "Transaction did not contain script output"
            <> "for public key '"
            <> T.pack (show pk)
            <> "'"
        [o] -> pure $ scriptTxIn o (pkValidator pk) unitRedeemer unitData
        _ -> throwing _OtherError $
            "Transaction contained multiple script outputs"
            <> "for public key '"
            <> T.pack (show pk)
            <> "'"
    pure ref
