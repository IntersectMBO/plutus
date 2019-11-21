{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Implements an n-out-of-m multisig contract.
module Language.PlutusTx.Coordination.Contracts.MultiSig
    ( MultiSig(..)
    , msValidator
    , validate
    , msAddress
    , lock
    , initialise
    , unlockTx
    ) where

import qualified Data.Map                     as Map
import qualified Data.Set                     as Set
import           Data.Foldable                (foldMap)
import           Language.PlutusTx.Prelude    hiding (foldMap)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       as Ledger hiding (initialise, to)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            as V
import           Wallet.API                   as WAPI

data MultiSig = MultiSig
                { signatories :: [Ledger.PubKey]
                -- ^ List of public keys of people who may sign the transaction
                , requiredSignatures :: Integer
                -- ^ Minimum number of signatures required to unlock
                --   the output (should not exceed @length signatories@)
                }
PlutusTx.makeLift ''MultiSig

validate :: MultiSig -> () -> () -> PendingTx -> Bool
validate (MultiSig keys num) _ _ p =
    let present = length (filter (V.txSignedBy p) keys)
    in present >= num

msValidator :: MultiSig -> ValidatorScript
msValidator sig = mkValidatorScript $
    $$(PlutusTx.compile [|| validatorParam ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode sig
    where validatorParam s = Scripts.wrapValidator (validate s)

-- | The address of a 'MultiSig' contract.
msAddress :: MultiSig -> Address
msAddress = Ledger.scriptAddress . msValidator

-- | Lock some funds in a 'MultiSig' contract.
lock :: (WalletAPI m, WalletDiagnostics m) => MultiSig -> Value -> m ()
lock ms vl = payToScript_ defaultSlotRange (msAddress ms) vl unitData

-- | Instruct the wallet to start watching the contract address
initialise :: (WalletAPI m) => MultiSig -> m ()
initialise = startWatching . msAddress

-- | Create a transaction that unlocks the funds. It has the signature of the
--   current wallet attached.
unlockTx :: (Monad m, WalletAPI m) => MultiSig -> m Tx
unlockTx ms = do
    let
        validator = msValidator ms
        address   = msAddress ms

    utxos <- WAPI.outputsAt address

    let

        mkIn :: TxOutRef -> TxIn
        mkIn r = Ledger.scriptTxIn r validator unitRedeemer unitData

        ins = Set.map mkIn (Map.keysSet utxos)
        val = foldMap (Ledger.txOutValue . Ledger.txOutTxOut) utxos

    ownOutput <- WAPI.ownPubKeyTxOut val

    let tx = Ledger.Tx
                { txInputs = ins
                , txOutputs = [ownOutput]
                , txForge = zero
                , txFee   = zero
                , txValidRange = defaultSlotRange
                , txSignatures = Map.empty
                , txData = Map.empty
                }

    signTxn tx
