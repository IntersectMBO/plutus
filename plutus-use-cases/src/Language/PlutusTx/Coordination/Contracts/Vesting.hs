{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
-- $vesting
module Language.PlutusTx.Coordination.Contracts.Vesting (
    VestingParams(..),
    VestingSchema,
    VestingTranche(..),
    totalAmount,
    vestingContract,
    validate,
    vestingScript
    ) where

import           Control.Lens
import           Control.Monad.Reader
import           Data.Foldable (fold)
import qualified Data.Text as T

import           GHC.Generics                 (Generic)
import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx  as Tx
import qualified Language.Plutus.Contract.Typed.Tx as Typed
import           Language.PlutusTx.Prelude    hiding (fold)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (Address, DataScript (..), Slot(..), PubKey (..), ValidatorScript, TxOut)
import qualified Ledger.AddressMap            as AM
import qualified Ledger.Interval              as Interval
import qualified Ledger.Slot                  as Slot
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import qualified Ledger.Validation            as Validation
import           Ledger.Validation            (PendingTx, PendingTx' (..))

-- $vesting
-- A simple vesting contract that locks some funds until a
-- predefined slot has been reached.

type VestingSchema =
    BlockchainActions
        .\/ Endpoint "vest funds" ()
        .\/ Endpoint "retrieve funds" Value

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    vestingTrancheAmount :: Value
    } deriving Generic

PlutusTx.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount can be spent.
data VestingParams = VestingParams {
    vestingTranche1 :: VestingTranche,
    vestingTranche2 :: VestingTranche,
    vestingOwner    :: PubKey
    } deriving Generic

PlutusTx.makeLift ''VestingParams

{-# INLINABLE totalAmount #-}
-- | The total amount vested
totalAmount :: VestingParams -> Value
totalAmount VestingParams{vestingTranche1,vestingTranche2} =
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

{-# INLINABLE remainingFrom #-}
-- | The amount that has not been released from this tranche yet
remainingFrom :: VestingTranche -> Slot.SlotRange -> Value
remainingFrom t@VestingTranche{vestingTrancheAmount} range =
    vestingTrancheAmount - availableFrom t range

{-# INLINABLE validate #-}
validate :: VestingParams -> () -> () -> PendingTx -> Bool
validate VestingParams{vestingTranche1, vestingTranche2, vestingOwner} () () ptx@PendingTx{pendingTxValidRange} =
    let
        remainingActual  = Validation.valueLockedBy ptx (Validation.ownHash ptx)

        remainingExpected = 
            remainingFrom vestingTranche1 pendingTxValidRange
            + remainingFrom vestingTranche2 pendingTxValidRange

    in remainingActual `Value.geq` remainingExpected
            && Validation.txSignedBy ptx vestingOwner

data Vesting
instance Scripts.ScriptType Vesting where
    type instance RedeemerType Vesting = ()
    type instance DataType Vesting = ()

vestingScript :: VestingParams -> ValidatorScript
vestingScript = Scripts.validatorScript . scriptInstance

scriptInstance :: VestingParams -> Scripts.ScriptInstance Vesting
scriptInstance vesting = Scripts.Validator @Vesting
    ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode vesting)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @() @()
            
contractAddress :: VestingParams -> Ledger.Address
contractAddress = Scripts.scriptAddress . scriptInstance

vestingContract :: VestingParams -> Contract VestingSchema T.Text ()
vestingContract vesting = vest <|> retrieve where
    retrieve = do
        payment <- endpoint @"retrieve funds"
        liveness <- retrieveFundsC vesting payment
        case liveness of
            Alive -> retrieve
            Dead  -> pure ()
    vest = endpoint @"vest funds" >> vestFundsC vesting

payIntoContract :: VestingParams -> Value -> TxOut
payIntoContract vp value = 
    Tx.scriptTxOut' 
        value 
        (contractAddress vp)
        (DataScript (PlutusTx.toData ()))

vestFundsC
    :: ( HasWriteTx s         
       )
    => VestingParams
    -> Contract s T.Text ()
vestFundsC vesting = do
    let tx = unbalancedTx [] [payIntoContract vesting (totalAmount vesting)]
    void $ writeTxSuccess tx

data Liveness = Alive | Dead

retrieveFundsC
    :: ( HasAwaitSlot s
       , HasUtxoAt s
       , HasWriteTx s
       )
    => VestingParams
    -> Value
    -> Contract s T.Text Liveness
retrieveFundsC vesting payment = do
    let addr = contractAddress vesting
    currentSlot <- awaitSlot 0
    unspentOutputs <- utxoAt addr
    let 
        currentlyLocked = fold (AM.values unspentOutputs)
        remainingValue = currentlyLocked - payment
        liveness = if remainingValue `Value.gt` mempty then Alive else Dead
        remainingOutputs = case liveness of
                            Alive -> [payIntoContract vesting remainingValue]
                            Dead  -> []
        tx = Typed.collectFromScriptFilter (\_ _ -> True) unspentOutputs (scriptInstance vesting) ()
                & validityRange .~ Interval.from currentSlot
                & requiredSignatures .~ [vestingOwner vesting]
                & outputs .~ remainingOutputs
    void $ writeTx tx
    return liveness
