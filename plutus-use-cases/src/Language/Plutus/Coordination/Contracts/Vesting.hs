-- | Vesting scheme as a PLC contract
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Language.Plutus.Coordination.Contracts.Vesting (
    Vesting(..),
    VestingTranche(..),
    VestingPLC(..),
    VestingData(..),
    vestFunds,
    retrieveFunds,
    validatorScript,
    totalAmount
    ) where

import           Control.Monad.Error.Class          (MonadError (..))
import qualified Data.Set                           as Set
import qualified Language.Plutus.CoreToPLC.Builtins as Builtins
import           Language.Plutus.Runtime            (Hash, Height, PendingTx (..), PendingTxIn (..), PendingTxOut (..),
                                                     PendingTxOutType (..), PubKey (..), Value)
import qualified Language.Plutus.Runtime.TH         as TH
import           Language.Plutus.TH                 (PlcCode, applyPlc, plutus)
import           Prelude                            hiding ((&&))
import           Wallet.API                         (WalletAPI (..), WalletAPIError, otherError, signAndSubmit)
import           Wallet.UTXO                        (DataScript (..), TxOutRef', Validator (..), scriptTxIn,
                                                     scriptTxOut)
import qualified Wallet.UTXO                        as UTXO

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Height,
    vestingTrancheAmount :: Value
    }

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (block height) after which an additional amount of money can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    vestingTranche2 :: VestingTranche,
    vestingOwner    :: PubKey
    }

-- | The total amount of money vested
totalAmount :: Vesting -> Value
totalAmount Vesting{..} =
    vestingTrancheAmount vestingTranche1 + vestingTrancheAmount vestingTranche2

newtype VestingPLC = VestingPLC PlcCode

-- | Data script for vesting utxo
data VestingData = VestingData {
    vestingDataHash    :: Hash, -- ^ Hash of the validator script
    vestingDataPaidOut :: Value -- ^ How much of the vested value has already been retrieved
    } deriving Eq

-- | Lock some funds with the vesting validator script and return a
--   [[VestingData]] representing the current state of the process
vestFunds :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => VestingPLC
    -> Vesting
    -> Value
    -> m VestingData
vestFunds c vst value = do
    _ <- if value < totalAmount vst then otherError "Value must not be smaller than vested amount" else pure ()
    let v' = UTXO.Value $ fromIntegral value
    (payment, change) <- createPaymentWithChange v'
    let vs = validatorScript c
        o = scriptTxOut v' vs d
        d = DataScript $(plutus [|
            let hashedVs = 1123 -- TODO: Should be `hash vs` (see [CGP-228])
            in VestingData hashedVs 0 |])
    signAndSubmit payment [o, change]
    pure $ VestingData 1123 0

-- | Retrieve some of the vested funds.
retrieveFunds :: (
    Monad m,
    WalletAPI m)
    => Vesting
    -> VestingPLC
    -> VestingData -- ^ Value that has already been taken out
    -> DataScript -- ^ the new vesting data reflecting the state of the
                  --   vesting process _after_ this transaction (TODO: Generate at runtime! [CGP-228])
    -> TxOutRef'  -- ^ Transaction output locked by the vesting validator script
    -> UTXO.Value -- ^ Value we want to take out now
    -> m VestingData
retrieveFunds vs vsPLC vd vdPLC r vnow = do
    oo <- payToPublicKey vnow
    let val = validatorScript vsPLC
        o   = scriptTxOut remaining val vdPLC
        remaining = (fromIntegral $ totalAmount vs) - vnow
        vd' = vd {vestingDataPaidOut = fromIntegral vnow + vestingDataPaidOut vd }
        inp = scriptTxIn r val UTXO.unitRedeemer
    signAndSubmit (Set.singleton inp) [oo, o]
    pure vd'

validatorScript :: VestingPLC -> Validator
validatorScript (VestingPLC v) = Validator val where
    val = applyPlc inner v
    inner = $(plutus [| \Vesting{..} () VestingData{..} (p :: PendingTx () VestingData) ->
        let

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $(TH.eqPubKey)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $( TH.and )

            PendingTx _ (_::[(PendingTxIn (), Value)]) os _ _ h _ = p
            VestingTranche d1 a1 = vestingTranche1
            VestingTranche d2 a2 = vestingTranche2

            -- We assume here that the txn outputs are always given in the same
            -- order (1 PubKey output, followed by 0 or 1 script outputs)
            amountSpent :: Value
            amountSpent = case os of
                ((PendingTxOut v' _ (PubKeyTxOut pk))::PendingTxOut VestingData):(_::[PendingTxOut VestingData])
                    | pk `eqPk` vestingOwner -> v'
                (_::[PendingTxOut VestingData]) -> Builtins.error ()

            -- Value that has been released so far under the scheme
            currentThreshold =
                if h >= d1
                then if h >= d2
                    -- everything can be spent
                     then a1 + a2
                     -- only the first tranche can be spent (we are between d1 and d2)
                     else a1
                -- Nothing has been released yet
                else 0

            newAmount = vestingDataPaidOut + amountSpent
            remainingAmount = a1 + a2 - newAmount

            -- Verify that the amount taken out, plus the amount already taken
            -- out before, does not exceed the threshold that is currently
            -- allowed
            amountsValid = newAmount <= currentThreshold

            -- Check that the remaining output is locked by the same validation
            -- script
            txnOutputsValid = case os of
                (_::PendingTxOut VestingData):(PendingTxOut v' (Just d') DataTxOut::PendingTxOut VestingData):(_::[PendingTxOut VestingData]) -> case d' of
                    VestingData h' po ->
                        h' == vestingDataHash
                        && po == newAmount
                        && v' == remainingAmount
                (_::[PendingTxOut VestingData]) -> Builtins.error ()

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else Builtins.error () |])

