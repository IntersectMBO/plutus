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
    , validator
    , validate
    ) where

import           Control.Monad                (void)
import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx  as Tx
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
contract = (lock <|> unlock) >> contract

validate :: MultiSig -> () -> () -> PendingTx -> Bool
validate MultiSig{signatories, minNumSignatures} _ _ p =
    let present = length (filter (V.txSignedBy p) signatories)
    in traceIfFalseH "not enough signatures" (present >= minNumSignatures)

validator :: MultiSig -> Validator
validator sig = mkValidatorScript $
    $$(PlutusTx.compile [|| validatorParam ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode sig
    where validatorParam s = Scripts.wrapValidator (validate s)

-- | Lock some funds in a 'MultiSig' contract.
lock :: AsContractError e => Contract MultiSigSchema e ()
lock = do
    (ms, vl) <- endpoint @"lock"
    let tx = payToScript vl (Ledger.scriptAddress (validator ms)) unitData
    void  $ submitTx tx

-- | The @"unlock"@ endpoint, unlocking some funds with a list
--   of signatures.
unlock :: AsContractError e => Contract MultiSigSchema e ()
unlock = do
    (ms, pks) <- endpoint @"unlock"
    let val = validator ms
    utx <- utxoAt (Ledger.scriptAddress val)
    let tx = collectFromScript utx val unitRedeemer
                <> foldMap Tx.mustBeSignedBy pks
    void $ submitTx tx
