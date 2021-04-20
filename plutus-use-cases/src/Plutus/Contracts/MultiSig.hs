{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Implements an n-out-of-m multisig contract.
module Plutus.Contracts.MultiSig
    ( MultiSig(..)
    , MultiSigSchema
    , contract
    , lock
    , scriptInstance
    , validate
    ) where

import           Control.Monad            (void)
import           Data.Aeson               (FromJSON, ToJSON)
import           GHC.Generics             (Generic)
import           Ledger
import qualified Ledger.Constraints       as Constraints
import           Ledger.Contexts          as V
import qualified Ledger.Typed.Scripts     as Scripts
import           Plutus.Contract
import qualified Plutus.Contract.Typed.Tx as Tx
import qualified PlutusTx                 as PlutusTx
import           PlutusTx.Prelude         hiding (Semigroup (..), foldMap)

import           Prelude                  (Semigroup (..), foldMap)

type MultiSigSchema =
    BlockchainActions
        .\/ Endpoint "lock" (MultiSig, Value)
        .\/ Endpoint "unlock" (MultiSig, [PubKeyHash])

data MultiSig =
        MultiSig
                { signatories      :: [Ledger.PubKeyHash]
                -- ^ List of public keys of people who may sign the transaction
                , minNumSignatures :: Integer
                -- ^ Minimum number of signatures required to unlock
                --   the output (should not exceed @length signatories@)
                } deriving stock (Show, Generic)
                  deriving anyclass (ToJSON, FromJSON)

PlutusTx.makeLift ''MultiSig

contract :: AsContractError e => Contract () MultiSigSchema e ()
contract = (lock `select` unlock) >> contract

{-# INLINABLE validate #-}
validate :: MultiSig -> () -> () -> ScriptContext -> Bool
validate MultiSig{signatories, minNumSignatures} _ _ p =
    let present = length (filter (V.txSignedBy (scriptContextTxInfo p)) signatories)
    in traceIfFalse "not enough signatures" (present >= minNumSignatures)

instance Scripts.ScriptType MultiSig where
    type instance RedeemerType MultiSig = ()
    type instance DatumType MultiSig = ()

scriptInstance :: MultiSig -> Scripts.ScriptInstance MultiSig
scriptInstance = Scripts.validatorParam @MultiSig
    $$(PlutusTx.compile [|| validate ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator


-- | Lock some funds in a 'MultiSig' contract.
lock :: AsContractError e => Contract () MultiSigSchema e ()
lock = do
    (ms, vl) <- endpoint @"lock"
    let tx = Constraints.mustPayToTheScript () vl
    let inst = scriptInstance ms
    void $ submitTxConstraints inst tx

-- | The @"unlock"@ endpoint, unlocking some funds with a list
--   of signatures.
unlock :: AsContractError e => Contract () MultiSigSchema e ()
unlock = do
    (ms, pks) <- endpoint @"unlock"
    let inst = scriptInstance ms
    utx <- utxoAt (Scripts.scriptAddress inst)
    let tx = Tx.collectFromScript utx ()
                <> foldMap Constraints.mustBeSignedBy pks
    void $ submitTxConstraintsSpending inst utx tx
