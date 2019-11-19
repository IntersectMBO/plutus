{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
module Wallet.Emulator.NodeClient where

import           Control.Lens        hiding (index)
import           Control.Monad.State
import           Data.Aeson          (FromJSON, ToJSON)
import           Data.List           (partition)
import           Data.Maybe          (isNothing)
import           Data.Traversable    (for)
import           GHC.Generics        (Generic)

import           Ledger              (Blockchain, Slot (..), Tx (..), TxId, lastSlot, txId)
import qualified Ledger.Index        as Index
import qualified Ledger.Interval     as Interval


-- | Events produced by the blockchain emulator.
data ChainEvent =
    TxnSubmit TxId
    -- ^ A transaction has been added to the pool of pending transactions.
    | TxnValidate TxId
    -- ^ A transaction has been validated and added to the blockchain.
    | TxnValidationFail TxId Index.ValidationError
    -- ^ A transaction failed  to validate.
    | SlotAdd Slot
    deriving (Eq, Show, Generic)

instance FromJSON ChainEvent
instance ToJSON ChainEvent

-- | The result of validating a block.
data ValidatedBlock = ValidatedBlock
    { vlbValid  :: [Tx]
    -- ^ The transactions that have been validated in this block.
    , vlbEvents :: [ChainEvent]
    -- ^ Transaction validation events for the transactions in this block.
    , vlbRest   :: [Tx]
    -- ^ The transactions that haven't been validated because the current slot is
    --   not in their validation interval.
    }

-- | A pool of transactions which have yet to be validated.
type TxPool = [Tx]

data ChainState = ChainState {
    _chainNewestFirst :: Blockchain, -- ^ The current chain, with the newest transactions first in the list.
    _txPool           :: TxPool, -- ^ The pool of pending transactions.
    _index            :: Index.UtxoIndex -- ^ The UTxO index, used for validation.
} deriving (Show)

emptyChainState :: ChainState
emptyChainState = ChainState [] [] mempty

makeLenses ''ChainState

-- | Validate a block given the current slot and UTxO index, returning the valid
--   transactions, success/failure events, remaining transactions and the
--   updated UTxO set.
validateBlock :: Slot -> Index.UtxoIndex -> [Tx] -> (ValidatedBlock, Index.UtxoIndex)
validateBlock slot@(Slot s) idx txns =
    let
        -- Select those transactions that can be validated in the
        -- current slot
        (eligibleTxns, rest) = partition (canValidateNow slot) txns

        -- Validate eligible transactions, updating the UTXO index each time
        (processed, idx') =
            flip runState idx $ for eligibleTxns $ \t -> do
                r <- validateEm slot t
                pure (t, r)

        -- The new block contains all transaction that were validated
        -- successfully
        block = fst <$> filter (isNothing . snd) processed

        -- Also return an `EmulatorEvent` for each transaction that was
        -- processed
        nextSlot = Slot (s + 1)
        events   = SlotAdd nextSlot : (uncurry mkValidationEvent <$> processed)

    in (ValidatedBlock block events rest, idx')

-- | Check whether the given transaction can be validated in the given slot.
canValidateNow :: Slot -> Tx -> Bool
canValidateNow slot tx = Interval.member slot (txValidRange tx)

mkValidationEvent :: Tx -> Maybe Index.ValidationError -> ChainEvent
mkValidationEvent t result =
    case result of
        Nothing  -> TxnValidate (txId t)
        Just err -> TxnValidationFail (txId t) err

-- | Validate a transaction in the current emulator state.
validateEm :: MonadState Index.UtxoIndex m => Slot -> Tx -> m (Maybe Index.ValidationError)
validateEm h txn = do
    idx <- get
    let result = Index.runValidation (Index.validateTransaction h txn) idx
    case result of
        Left e -> pure (Just e)
        Right idx' -> do
            _ <- put idx'
            pure Nothing

class Monad m => NodeClientAPI m where
    publishTx :: Tx -> m ()
    currentSlot :: m Slot

-- | Pure implementation of the NodeClient API

instance NodeClientAPI (State ChainState) where
    publishTx tx = state $ ((), ) . over txPool (tx :)

    currentSlot =
        gets (Slot . fromIntegral . length . _chainNewestFirst)

processBlock :: MonadState ChainState m => m ValidatedBlock
processBlock = state $ \st ->
    let pool  = st ^. txPool
        chain = st ^. chainNewestFirst
        slot  = lastSlot chain
        idx   = st ^. index
        (validatedBlock, idx') =
            validateBlock slot idx pool
        newChain = vlbValid validatedBlock : chain
    in  (validatedBlock, st & txPool .~ vlbRest validatedBlock
                            & chainNewestFirst .~ newChain
                            & index .~ idx')

