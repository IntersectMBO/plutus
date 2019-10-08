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

import           Data.Maybe (listToMaybe)
import qualified Data.Map   as Map
import qualified Data.Text  as Text

import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       as Ledger hiding (initialise, to)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            as V

import           Language.Plutus.Contract     as Contract

mkValidator :: PubKey -> () -> () -> PendingTx -> Bool
mkValidator pk' _ _ p = V.txSignedBy p pk'

pkValidator :: PubKey -> ValidatorScript
pkValidator pk = ValidatorScript $
    Ledger.fromCompiledCode $$(PlutusTx.compile [|| validatorParam ||])
        `Ledger.applyScript`
            Ledger.lifted pk
    where validatorParam k = Scripts.wrapValidator (mkValidator k)

-- | Lock some funds in a 'PayToPubKey' contract, returning the output's address
--   and a 'TxIn' transaction input that can spend it.
pubKeyContract 
    :: forall s.
    ( HasWatchAddress s
    , HasWriteTx s)
    => PubKey
    -> Value
    -> Contract s TxIn
pubKeyContract pk vl = do
    let address = Ledger.scriptAddress (pkValidator pk)
        tx = Contract.payToScript vl address (DataScript $ PlutusTx.toData ())
    txId <- writeTxSuccess tx

    ledgerTx <- awaitTransactionConfirmed address txId 
    let output = listToMaybe
                $ fmap fst
                $ filter ((==) address . txOutAddress . snd)
                $ Map.toList
                $ unspentOutputsTx ledgerTx
    ref <- case output of
        Nothing -> 
            throwContractError
            $ "transaction did not contain script output"
            <> "for public key '"
            <> Text.pack (show pk)
            <> "'"
        Just o -> pure $ scriptTxIn o (pkValidator pk) (RedeemerScript $ PlutusTx.toData ())
    pure ref
