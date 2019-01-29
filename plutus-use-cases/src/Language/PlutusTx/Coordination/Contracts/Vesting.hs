-- | Vesting scheme as a PLC contract
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
module Language.PlutusTx.Coordination.Contracts.Vesting (
    Vesting(..),
    VestingTranche(..),
    VestingData(..),
    vestFunds,
    retrieveFunds,
    validatorScript,
    totalAmount,
    validatorScriptHash
    ) where

import           Control.Monad.Error.Class    (MonadError (..))
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Ledger.Validation            (PendingTx (..), PendingTxOut (..), PendingTxOutType (..),
                                              ValidatorHash)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (DataScript (..), Slot(..), PubKey (..), TxOutRef, ValidatorScript (..), scriptTxIn, scriptTxOut)
import qualified Ledger                       as Ledger
import qualified Ledger.Interval              as Interval
import qualified Ledger.Validation            as Validation
import           Prelude                      hiding ((&&))
import qualified Wallet                       as W
import           Wallet                       (WalletAPI (..), WalletAPIError, throwOtherError, ownPubKeyTxOut, createTxAndSubmit, defaultSlotRange)
import           Ledger.Ada                   (Ada)
import qualified Ledger.Ada.TH                as Ada

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    vestingTrancheAmount :: Ada
    } deriving Generic

PlutusTx.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount of Ada can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    vestingTranche2 :: VestingTranche,
    vestingOwner    :: PubKey
    } deriving Generic

PlutusTx.makeLift ''Vesting

-- | The total amount of Ada vested
totalAmount :: Vesting -> Ada
totalAmount Vesting{..} =
    vestingTrancheAmount vestingTranche1 + vestingTrancheAmount vestingTranche2

-- | Data script for vesting utxo
data VestingData = VestingData {
    vestingDataHash    :: ValidatorHash, -- ^ Hash of the validator script
    vestingDataPaidOut :: Ada            -- ^ How much of the vested value has already been retrieved
    } deriving (Eq, Generic)

PlutusTx.makeLift ''VestingData

-- | Lock some funds with the vesting validator script and return a
--   [[VestingData]] representing the current state of the process
vestFunds :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Vesting
    -> Ada
    -> m VestingData
vestFunds vst adaAmount = do
    _ <- if adaAmount < totalAmount vst then throwOtherError "Value must not be smaller than vested amount" else pure ()
    let value = $$(Ada.toValue) adaAmount
    (payment, change) <- createPaymentWithChange value
    let vs = validatorScript vst
        o = scriptTxOut value vs (DataScript $ Ledger.lifted vd)
        vd =  VestingData (validatorScriptHash vst) 0
    _ <- createTxAndSubmit defaultSlotRange payment (o : maybeToList change)
    pure vd

-- | Retrieve some of the vested funds.
retrieveFunds :: (
    Monad m,
    WalletAPI m)
    => Vesting
    -- ^ Definition of vesting scheme
    -> VestingData 
    -- ^ Value that has already been taken out
    -> TxOutRef    
    -- ^ Transaction output locked by the vesting validator script
    -> Ada         
    -- ^ Value we want to take out now
    -> m VestingData
retrieveFunds vs vd r anow = do
    let vnow = $$(Ada.toValue) anow
    oo <- ownPubKeyTxOut vnow
    currentSlot <- slot
    let val = validatorScript vs
        o   = scriptTxOut remaining val (DataScript $ Ledger.lifted vd')
        remaining = $$(Ada.toValue) (totalAmount vs - anow)
        vd' = vd {vestingDataPaidOut = anow + vestingDataPaidOut vd }
        inp = scriptTxIn r val Ledger.unitRedeemer
        range = W.intervalFrom currentSlot
    _ <- createTxAndSubmit range (Set.singleton inp) [oo, o]
    pure vd'

validatorScriptHash :: Vesting -> ValidatorHash
validatorScriptHash =
    Validation.plcValidatorDigest
    . Ledger.getAddress
    . Ledger.scriptAddress
    . validatorScript

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript val where
    val = Ledger.applyScript inner (Ledger.lifted v)
    inner = $$(Ledger.compileScript [|| \Vesting{..} () VestingData{..} (p :: PendingTx) ->
        let

            eqBs :: ValidatorHash -> ValidatorHash -> Bool
            eqBs = $$(Validation.eqValidator)

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $$(Validation.eqPubKey)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            PendingTx _ os _ _ _ range = p
            VestingTranche d1 a1 = vestingTranche1
            VestingTranche d2 a2 = vestingTranche2

            -- We assume here that the txn outputs are always given in the same
            -- order (1 PubKey output, followed by 0 or 1 script outputs)
            amountSpent :: Ada
            amountSpent = case os of
                PendingTxOut v' _ (PubKeyTxOut pk):_
                    | pk `eqPk` vestingOwner -> $$(Ada.fromValue) v'
                _ -> $$(PlutusTx.error) ()

            -- Value that has been released so far under the scheme
            currentThreshold =
                if $$(Interval.contains) ($$(Interval.from) d1) range
                then if $$(Interval.contains) ($$(Interval.from) d2) range
                    -- everything can be spent
                     then $$(Ada.plus) a1 a2
                     -- only the first tranche can be spent (we are between d1 and d2)
                     else a1
                -- Nothing has been released yet
                else $$(Ada.zero)

            paidOut = vestingDataPaidOut
            newAmount = $$(Ada.plus) paidOut amountSpent

            -- Verify that the amount taken out, plus the amount already taken
            -- out before, does not exceed the threshold that is currently
            -- allowed
            amountsValid = $$(Ada.leq) newAmount currentThreshold

            -- Check that the remaining output is locked by the same validation
            -- script
            txnOutputsValid = case os of
                _:PendingTxOut _ (Just (vl', _)) DataTxOut:_ ->
                    vl' `eqBs` vestingDataHash
                _ -> $$(PlutusTx.error) ()

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else $$(PlutusTx.error) () ||])
