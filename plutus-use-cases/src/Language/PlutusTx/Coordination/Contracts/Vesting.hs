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
    totalAmount,
    validatorScriptHash,
    -- * Script
    validatorScript
    ) where

import           Control.Monad.Error.Class    (MonadError (..))
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Ledger.Validation            (PendingTx (..), ValidatorHash)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (DataScript (..), Slot(..), PubKey (..), TxOutRef, ValidatorScript (..), scriptTxIn, scriptTxOut)
import qualified Ledger                       as Ledger
import qualified Ledger.Interval              as Interval
import qualified Ledger.Slot                  as Slot
import qualified Ledger.Validation            as Validation
import qualified Wallet                       as W
import           Wallet                       (WalletAPI (..), WalletAPIError, throwOtherError, ownPubKeyTxOut, createTxAndSubmit, defaultSlotRange)
import           Ledger.Ada                   (Ada)
import qualified Ledger.Ada                   as Ada

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
{-# INLINABLE totalAmount #-}
totalAmount :: Vesting -> Ada
totalAmount Vesting{..} =
    vestingTrancheAmount vestingTranche1 `Ada.plus` vestingTrancheAmount vestingTranche2

-- | The amount of Ada guaranteed to be available from a given tranche in a given slot range.
{-# INLINABLE availableFrom #-}
availableFrom :: VestingTranche -> Slot.SlotRange -> Ada
availableFrom (VestingTranche d v) range =
    -- The valid range is an open-ended range starting from the tranche vesting date
    let validRange = Interval.from d
    -- If the valid range completely contains the argument range (meaning in particular
    -- that the start slot of the argument range is after the tranche vesting date), then
    -- the money in the tranche is available, otherwise nothing is available.
    in if validRange `Slot.contains` range then v else Ada.zero

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
    let value = Ada.toValue adaAmount
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
    let vnow = Ada.toValue anow
    oo <- ownPubKeyTxOut vnow
    currentSlot <- slot
    let val = validatorScript vs
        o   = scriptTxOut remaining val (DataScript $ Ledger.lifted vd')
        remaining = Ada.toValue (totalAmount vs - anow)
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

mkValidator :: Vesting -> VestingData -> () -> PendingTx -> ()
mkValidator d@Vesting{..} VestingData{..} () p@PendingTx{pendingTxValidRange = range} =
    let
        -- We assume here that the txn outputs are always given in the same
        -- order (1 PubKey output, followed by 0 or 1 script outputs)
        amountSpent :: Ada
        amountSpent = Ada.fromValue (Validation.valuePaidTo p vestingOwner)

        -- Value that has been released so far under the scheme
        released = availableFrom vestingTranche1 range
            `Ada.plus` availableFrom vestingTranche2 range

        paidOut = vestingDataPaidOut
        newAmount = Ada.plus paidOut amountSpent

        -- Verify that the amount taken out, plus the amount already taken
        -- out before, does not exceed the threshold that is currently
        -- allowed
        amountsValid = newAmount `Ada.leq` released

        -- Check that the remaining output is locked by the same validation
        -- script
        txnOutputsValid =
            let remaining = Validation.adaLockedBy p (Validation.ownHash p) in
            remaining `Ada.eq` (totalAmount d `Ada.minus` newAmount)

        isValid = amountsValid `PlutusTx.and` txnOutputsValid
    in
    if isValid then () else PlutusTx.error ()

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript $
    $$(Ledger.compileScript [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted v
