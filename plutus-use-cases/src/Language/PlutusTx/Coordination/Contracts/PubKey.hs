{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A "pay-to-pubkey" transaction output implemented as a Plutus
--   contract. This is useful if you need something that behaves like
--   a pay-to-pubkey output, but is not (easily) identified by wallets
--   as one.
module Language.PlutusTx.Coordination.Contracts.PubKey(pubKeyContract, scriptInstance, PubKeyError(..), AsPubKeyError(..)) where

import           Control.Lens
import           Control.Monad.Error.Lens
import           Data.Aeson               (FromJSON, ToJSON)
import qualified Data.Map                 as Map
import           GHC.Generics             (Generic)

import qualified Language.PlutusTx        as PlutusTx
import           Ledger                   as Ledger hiding (initialise, to)
import           Ledger.Contexts          as V
import           Ledger.Typed.Scripts     (ScriptInstance)
import qualified Ledger.Typed.Scripts     as Scripts

import           Language.Plutus.Contract as Contract
import qualified Ledger.Constraints       as Constraints

mkValidator :: PubKeyHash -> () -> () -> ValidatorCtx -> Bool
mkValidator pk' _ _ p = V.txSignedBy (valCtxTxInfo p) pk'

data PubKeyContract

instance Scripts.ScriptType PubKeyContract where
    type instance RedeemerType PubKeyContract = ()
    type instance DatumType PubKeyContract = ()

scriptInstance :: PubKeyHash -> Scripts.ScriptInstance PubKeyContract
scriptInstance pk =
    Scripts.validator @PubKeyContract
        ($$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode pk)
        $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @() @()

data PubKeyError =
    ScriptOutputMissing PubKeyHash
    | MultipleScriptOutputs PubKeyHash
    | PKContractError ContractError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''PubKeyError

instance AsContractError PubKeyError where
    _ContractError = _PKContractError

-- | Lock some funds in a 'PayToPubKey' contract, returning the output's address
--   and a 'TxIn' transaction input that can spend it.
pubKeyContract
    :: forall w s e.
    ( HasWriteTx s
    , HasTxConfirmation s
    , AsPubKeyError e
    )
    => PubKeyHash
    -> Value
    -> Contract w s e (TxOutRef, TxOutTx, ScriptInstance PubKeyContract)
pubKeyContract pk vl = mapError (review _PubKeyError   ) $ do
    let inst = scriptInstance pk
        address = Scripts.scriptAddress inst
        tx = Constraints.mustPayToTheScript () vl

    ledgerTx <- submitTxConstraints inst tx

    _ <- awaitTxConfirmed (txId ledgerTx)
    let output = Map.toList
                $ Map.filter ((==) address . txOutAddress)
                $ unspentOutputsTx ledgerTx
    case output of
        []                   -> throwing _ScriptOutputMissing pk
        [(outRef, outTxOut)] -> pure (outRef, TxOutTx{txOutTxTx = ledgerTx, txOutTxOut = outTxOut}, inst)
        _                    -> throwing _MultipleScriptOutputs pk
