-- | Vesting scheme as a PLC contract
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
module Language.PlutusTx.Coordination.Contracts.Vesting (
    Vesting(..),
    VestingTranche(..),
    VestingData(..),
    vestFunds,
    retrieveFunds,
    totalAmount,
    validatorScriptHash,
    -- * Script
    validatorScript,
    mkValidator
    ) where

import           Control.Applicative          (Applicative (..))
import           Control.Monad.Error.Class    (MonadError (..))
import           Data.Maybe                   (maybeToList)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Prelude    hiding (Applicative (..))
import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Applicative as PlutusTx
import qualified Ledger                       as Ledger
import           Ledger                       (DataScript (..), Slot(..), PubKey (..), TxOutRef, RedeemerScript (..), ValidatorScript (..), scriptTxIn, scriptTxOut)
import qualified Ledger.Ada                   as Ada
import qualified Ledger.Interval              as Interval
import qualified Ledger.Slot                  as Slot
import           Ledger.Scripts               (ValidatorHash, HashedDataScript)
import qualified Ledger.Scripts               as Scripts
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import qualified Ledger.Validation            as Validation
import           Ledger.Validation            (PendingTx, PendingTx' (..), PendingTxIn'(..), PendingTxOut(..), getContinuingOutputs)
import qualified Wallet                       as W
import           Wallet                       (WalletAPI (..), WalletAPIError, throwOtherError, ownPubKeyTxOut, createTxAndSubmit, defaultSlotRange, createPaymentWithChange)

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    vestingTrancheAmount :: Value
    } deriving Generic

PlutusTx.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    vestingTranche2 :: VestingTranche,
    vestingOwner    :: PubKey
    } deriving Generic

PlutusTx.makeLift ''Vesting

{-# INLINABLE totalAmount #-}
-- | The total amount vested
totalAmount :: Vesting -> Value
totalAmount Vesting{..} =
    vestingTrancheAmount vestingTranche1 + vestingTrancheAmount vestingTranche2

{-# INLINABLE availableFrom #-}
-- | The amount guaranteed to be available from a given tranche in a given slot range.
availableFrom :: VestingTranche -> Slot.SlotRange -> Value
availableFrom (VestingTranche d v) range =
    -- The valid range is an open-ended range starting from the tranche vesting date
    let validRange = Interval.from d
    -- If the valid range completely contains the argument range (meaning in particular
    -- that the start slot of the argument range is after the tranche vesting date), then
    -- the money in the tranche is available, otherwise nothing is available.
    in if validRange `Interval.contains` range then v else zero

-- | Data script for vesting utxo
data VestingData = VestingData {
    vestingDataHash    :: ValidatorHash, -- ^ Hash of the validator script
    vestingDataPaidOut :: Value          -- ^ How much of the vested value has already been retrieved
    } deriving (Generic)

instance Eq VestingData where
    {-# INLINABLE (==) #-}
    (VestingData h1 v1) == (VestingData h2 v2) = h1 == h2 && v1 == v2

instance PlutusTx.IsData VestingData where
    {-# INLINABLE toData #-}
    toData (VestingData h v) = PlutusTx.Constr 0 [PlutusTx.toData h, PlutusTx.toData v]
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [h, v]) | i == 0 = VestingData <$> PlutusTx.fromData h PlutusTx.<*> PlutusTx.fromData v
    fromData _ = Nothing

PlutusTx.makeLift ''VestingData

transactionFee :: Value
transactionFee = Ada.lovelaceValueOf 0

-- | Lock some funds with the vesting validator script and return a
--   [[VestingData]] representing the current state of the process
vestFunds :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Vesting
    -> Value
    -> m VestingData
vestFunds vst value = do
    _ <- if value `Value.lt` totalAmount vst then throwOtherError "Value must not be smaller than vested amount" else pure ()
    (payment, change) <- createPaymentWithChange (value + transactionFee)
    let vs = validatorScript vst
        o = scriptTxOut value vs (DataScript $  Ledger.lifted $ PlutusTx.toData vd)
        vd =  VestingData (validatorScriptHash vst) zero
    _ <- createTxAndSubmit defaultSlotRange payment (o : maybeToList change)
    pure vd

redeemerScript :: RedeemerScript
redeemerScript = RedeemerScript $ $$(Ledger.compileScript [|| \(_ :: Sealed (HashedDataScript PlutusTx.Data)) -> PlutusTx.toData () ||])

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
    -> Value
    -- ^ Value we want to take out now
    -> m VestingData
retrieveFunds vs vd r vnow = do
    oo <- ownPubKeyTxOut vnow
    currentSlot <- slot
    let val = validatorScript vs
        o   = scriptTxOut remaining val (DataScript $ Ledger.lifted $ PlutusTx.toData vd')
        remaining = totalAmount vs - vnow
        vd' = vd {vestingDataPaidOut = vnow + vestingDataPaidOut vd }
        inp = scriptTxIn r val redeemerScript
        range = W.intervalFrom currentSlot
    (fee, change) <- createPaymentWithChange transactionFee
    _ <- createTxAndSubmit range (Set.insert inp fee) ([oo, o] ++ maybeToList change)
    pure vd'

validatorScriptHash :: Vesting -> ValidatorHash
validatorScriptHash =
    Scripts.plcValidatorDigest
    . Ledger.getAddress
    . Ledger.scriptAddress
    . validatorScript

{-# INLINABLE mkValidator #-}
mkValidator :: Vesting -> PlutusTx.Data -> PlutusTx.Data -> PendingTx -> Bool
mkValidator d@Vesting{..} (PlutusTx.fromData -> Just (VestingData{..})) _ ptx@PendingTx{pendingTxValidRange = range} =
    let
        -- The locked funds which are returned?
        payBack :: Value
        payBack = mconcat (map pendingTxOutValue (getContinuingOutputs ptx))

        -- The funds available in the contract.
        lockedValue :: Value
        lockedValue = pendingTxInValue (pendingTxIn ptx)

        -- The funds that are paid to the owner
        amountSpent :: Value
        amountSpent = lockedValue - payBack

        -- Value that has been released so far under the scheme
        released = availableFrom vestingTranche1 range
            + availableFrom vestingTranche2 range

        paidOut = vestingDataPaidOut
        newAmount = paidOut + amountSpent

        -- Verify that the amount taken out, plus the amount already taken
        -- out before, does not exceed the threshold that is currently
        -- allowed
        amountsValid = newAmount `Value.leq` released

        -- Check that the remaining output is locked by the same validation
        -- script
        txnOutputsValid =
            let remaining = Validation.valueLockedBy ptx (Validation.ownHash ptx) in
            remaining == (totalAmount d - newAmount)

    in amountsValid && txnOutputsValid
mkValidator _ _ _ _ = False

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript $
    $$(Ledger.compileScript [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted v
