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
module Language.PlutusTx.Coordination.Contracts.Vesting (
    -- $vesting
    VestingParams(..),
    VestingSchema,
    VestingTranche(..),
    VestingError(..),
    AsVestingError(..),
    totalAmount,
    vestingContract,
    validate,
    vestingScript
    ) where

import Control.Lens
import           Control.Monad        (void, when)
import qualified Data.Map as Map
import           Prelude (Semigroup(..))

import           GHC.Generics                 (Generic)
import           Language.Plutus.Contract     hiding (when)
import qualified Language.Plutus.Contract.Typed.Tx as Typed
import           Language.PlutusTx.Prelude    hiding (Semigroup(..), fold)
import qualified Language.PlutusTx            as PlutusTx
import Ledger.Constraints (TxConstraints, mustPayToTheScript, mustValidateIn, mustBeSignedBy)
import           Ledger                       (Address, Slot(..), PubKeyHash (..), Validator)
import qualified Ledger.Interval              as Interval
import qualified Ledger.Slot                  as Slot
import Ledger.Typed.Scripts (ScriptType(..))
import qualified Ledger.Typed.Scripts         as Scripts
import qualified Ledger.Tx as Tx
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import qualified Ledger.Validation            as Validation
import           Ledger.Validation            (PendingTx, PendingTx' (..))
import qualified Prelude as Haskell 

{- |
    A simple vesting scheme. Money is locked by a contract and may only be
    retrieved after some time has passed.

    This is our first example of a contract that covers multiple transactions,
    with a contract state that changes over time.

    In our vesting scheme the money will be released in two _tranches_ (parts):
    A smaller part will be available after an initial number of slots have
    passed, and the entire amount will be released at the end. The owner of the
    vesting scheme does not have to take out all the money at once: They can
    take out any amount up to the total that has been released so far. The
    remaining funds stay locked and can be retrieved later.

    Let's start with the data types.

-}

type VestingSchema =
    BlockchainActions
        .\/ Endpoint "vest funds" ()
        .\/ Endpoint "retrieve funds" Value

data Vesting

instance ScriptType Vesting where
    type instance RedeemerType Vesting = ()
    type instance DatumType Vesting = ()

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
    vestingOwner    :: PubKeyHash
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

availableAt :: VestingParams -> Slot -> Value
availableAt VestingParams{vestingTranche1, vestingTranche2} sl =
    let f VestingTranche{vestingTrancheDate, vestingTrancheAmount} =
            if sl >= vestingTrancheDate then vestingTrancheAmount else mempty
    in foldMap f [vestingTranche1, vestingTranche2]

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
            -- The policy encoded in this contract
            -- is "vestingOwner can do with the funds what they want" (as opposed
            -- to "the funds must be paid to vestingOwner"). This is enforcey by
            -- the following condition:
            && Validation.txSignedBy ptx vestingOwner
            -- That way the recipient of the funds can pay them to whatever address they
            -- please, potentially saving one transaction.

vestingScript :: VestingParams -> Validator
vestingScript = Scripts.validatorScript . scriptInstance

scriptInstance :: VestingParams -> Scripts.ScriptInstance Vesting
scriptInstance vesting = Scripts.validator @Vesting
    ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode vesting)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @() @()

contractAddress :: VestingParams -> Ledger.Address
contractAddress = Scripts.scriptAddress . scriptInstance

data VestingError =
    VContractError ContractError
    | InsufficientFundsError Value Value Value
    deriving (Haskell.Eq, Show)

makeClassyPrisms ''VestingError

instance AsContractError VestingError where
    _ContractError = _VContractError

vestingContract :: AsVestingError e => VestingParams -> Contract VestingSchema e ()
vestingContract vesting = mapError (review _VestingError) (vest `select` retrieve)
  where
    vest = endpoint @"vest funds" >> vestFundsC vesting
    retrieve = do
        payment <- endpoint @"retrieve funds"
        liveness <- retrieveFundsC vesting payment
        case liveness of
            Alive -> retrieve
            Dead  -> pure ()

payIntoContract :: Value -> TxConstraints () ()
payIntoContract value = mustPayToTheScript () value

vestFundsC
    :: ( HasWriteTx s
       , AsVestingError e
       )
    => VestingParams
    -> Contract s e ()
vestFundsC vesting = mapError (review _VestingError) $ do
    let tx = payIntoContract (totalAmount vesting)
    void $ submitTxConstraints (scriptInstance vesting) tx

data Liveness = Alive | Dead

retrieveFundsC
    :: ( HasAwaitSlot s
       , HasUtxoAt s
       , HasWriteTx s
       , AsVestingError e
       )
    => VestingParams
    -> Value
    -> Contract s e Liveness
retrieveFundsC vesting payment = mapError (review _VestingError) $ do
    let inst = scriptInstance vesting
        addr = Scripts.scriptAddress inst
    nextSlot <- awaitSlot 0
    unspentOutputs <- utxoAt addr
    let
        currentlyLocked = foldMap (Validation.txOutValue . Tx.txOutTxOut . snd) (Map.toList unspentOutputs)
        remainingValue = currentlyLocked - payment
        mustRemainLocked = totalAmount vesting - availableAt vesting nextSlot
        maxPayment = currentlyLocked - mustRemainLocked

    when (remainingValue `Value.lt` mustRemainLocked)
        $ throwError
        $ InsufficientFundsError payment maxPayment mustRemainLocked

    let liveness = if remainingValue `Value.gt` mempty then Alive else Dead
        remainingOutputs = case liveness of
                            Alive -> payIntoContract remainingValue
                            Dead  -> mempty
        tx = Typed.collectFromScript unspentOutputs ()
                <> remainingOutputs
                <> mustValidateIn (Interval.from nextSlot)
                <> mustBeSignedBy (vestingOwner vesting)
                -- we don't need to add a pubkey output for 'vestingOwner' here
                -- because this will be done by the wallet when it balances the
                -- transaction.
    void $ submitTxConstraintsSpending inst unspentOutputs tx
    return liveness
