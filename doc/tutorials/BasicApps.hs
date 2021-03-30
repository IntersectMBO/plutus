{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module BasicApps where

-- BLOCK0

import           Control.Monad          (void)
import           Data.Aeson             (FromJSON, ToJSON)
import qualified Data.Text              as T
import           GHC.Generics           (Generic)
import           Ledger
import qualified Ledger.Ada             as Ada
import qualified Ledger.Constraints     as Constraints
import qualified Ledger.Typed.Scripts   as Scripts
import           Plutus.Contract
import qualified PlutusTx               as PlutusTx
import           PlutusTx.Prelude
import           Schema
import           Wallet.Emulator.Wallet

-- BLOCK1

data SplitData =
    SplitData
        { recipient1 :: PubKeyHash -- ^ First recipient of the funds
        , recipient2 :: PubKeyHash -- ^ Second recipient of the funds
        , amount     :: Ada -- ^ How much Ada we want to lock
        }
    deriving stock (Show, Generic)

-- For a 'real' application use 'makeIsDataIndexed' to ensure the output is stable over time
PlutusTx.unstableMakeIsData ''SplitData
PlutusTx.makeLift ''SplitData

-- BLOCK2

validateSplit :: SplitData -> () -> ValidatorCtx -> Bool
validateSplit SplitData{recipient1, recipient2, amount} _ ValidatorCtx{valCtxTxInfo} =
    let half = Ada.divide amount 2 in
    Ada.fromValue (valuePaidTo valCtxTxInfo recipient1) >= half &&
    Ada.fromValue (valuePaidTo valCtxTxInfo recipient2) >= (amount - half)

-- BLOCK3

data Split
instance Scripts.ScriptType Split where
    type instance RedeemerType Split = ()
    type instance DatumType Split = SplitData

splitInstance :: Scripts.ScriptInstance Split
splitInstance = Scripts.validator @Split
    $$(PlutusTx.compile [|| validateSplit ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @SplitData @()

-- BLOCK4

data LockArgs =
        LockArgs
            { recipient1Wallet :: Wallet
            , recipient2Wallet :: Wallet
            , totalAda         :: Ada
            }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON, ToSchema)

type SplitSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockArgs
        .\/ Endpoint "unlock" LockArgs

-- BLOCK5

lock :: Contract () SplitSchema T.Text LockArgs
lock = endpoint @"lock"

unlock :: Contract () SplitSchema T.Text LockArgs
unlock = endpoint @"unlock"

-- BLOCK6

mkSplitData :: LockArgs -> SplitData
mkSplitData LockArgs{recipient1Wallet, recipient2Wallet, totalAda} =
    let convert :: Wallet -> PubKeyHash
        convert = pubKeyHash . walletPubKey
    in
    SplitData
        { recipient1 = convert recipient1Wallet
        , recipient2 = convert recipient2Wallet
        , amount = totalAda
        }

-- BLOCK7

lockFunds :: SplitData -> Contract () SplitSchema T.Text ()
lockFunds s@SplitData{amount} = do
    logInfo $ "Locking " <> show amount
    let tx = Constraints.mustPayToTheScript s (Ada.toValue amount)
    void $ submitTxConstraints splitInstance tx

-- BLOCK8

unlockFunds :: SplitData -> Contract () SplitSchema T.Text ()
unlockFunds SplitData{recipient1, recipient2, amount} = do
    let contractAddress = (Ledger.scriptAddress (Scripts.validatorScript splitInstance))
    utxos <- utxoAt contractAddress
    let half = Ada.divide amount 2
        tx =
            collectFromScript utxos ()
            <> Constraints.mustPayToPubKey recipient1 (Ada.toValue half)
            <> Constraints.mustPayToPubKey recipient2 (Ada.toValue $ amount - half)
    void $ submitTxConstraintsSpending splitInstance utxos tx

-- BLOCK9

endpoints :: Contract SplitSchema T.Text ()
-- BLOCK10

endpoints = (lock >>= lockFunds . mkSplitData) `select` (unlock >>= unlockFunds . mkSplitData)

-- BLOCK11
