{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Implements an n-out-of-m multisig contract.
module Language.PlutusTx.Coordination.Contracts.MultiSig
    ( MultiSig(..)
    , MultiSigSchema
    , contract
    , lock
    , scriptInstance
    , validate
    ) where

import           Control.Monad                (void)
import           Language.Plutus.Contract
import qualified Ledger.Constraints           as Constraints
import qualified Language.Plutus.Contract.Typed.Tx  as Tx
import           Language.PlutusTx.Prelude    hiding (Semigroup(..), foldMap)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            as V

import           Prelude                      (Semigroup(..), foldMap)

type MultiSigSchema =
    BlockchainActions
        .\/ Endpoint "lock" (MultiSig, Value)
        .\/ Endpoint "unlock" (MultiSig, [PubKeyHash])

data MultiSig =
        MultiSig
                { signatories :: [Ledger.PubKeyHash]
                -- ^ List of public keys of people who may sign the transaction
                , minNumSignatures :: Integer
                -- ^ Minimum number of signatures required to unlock
                --   the output (should not exceed @length signatories@)
                } deriving Show

PlutusTx.makeLift ''MultiSig

contract :: AsContractError e => Contract MultiSigSchema e ()
contract = (lock `select` unlock) >> contract

{-# INLINABLE validate #-}
validate :: MultiSig -> () -> () -> ValidatorCtx -> Bool
validate MultiSig{signatories, minNumSignatures} _ _ p =
    let present = length (filter (V.txSignedBy (valCtxTxInfo p)) signatories)
    in traceIfFalse "not enough signatures" (present >= minNumSignatures)

instance Scripts.ScriptType MultiSig where
    type instance RedeemerType MultiSig = ()
    type instance DatumType MultiSig = ()

scriptInstance :: MultiSig -> Scripts.ScriptInstance MultiSig
scriptInstance ms =
    let wrap = Scripts.wrapValidator @() @() in
    Scripts.validator @MultiSig
        ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode ms)
        $$(PlutusTx.compile [|| wrap ||])


-- | Lock some funds in a 'MultiSig' contract.
lock :: AsContractError e => Contract MultiSigSchema e ()
lock = do
    (ms, vl) <- endpoint @"lock"
    let tx = Constraints.mustPayToTheScript () vl
    let inst = scriptInstance ms
    void $ submitTxConstraints inst tx

-- | The @"unlock"@ endpoint, unlocking some funds with a list
--   of signatures.
unlock :: AsContractError e => Contract MultiSigSchema e ()
unlock = do
    (ms, pks) <- endpoint @"unlock"
    let inst = scriptInstance ms
    utx <- utxoAt (Scripts.scriptAddress inst)
    let tx = Tx.collectFromScript utx ()
                <> foldMap Constraints.mustBeSignedBy pks
    void $ submitTxConstraintsSpending inst utx tx
