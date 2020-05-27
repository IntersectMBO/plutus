{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
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
{-# LANGUAGE TypeOperators         #-}
module Wallet.Emulator.Chain where

import           Control.Lens               hiding (index)
import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer
import qualified Control.Monad.State        as S
import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.List                  (partition)
import           Data.Maybe                 (isNothing)
import           Data.Text.Prettyprint.Doc
import           Data.Traversable           (for)
import           GHC.Generics               (Generic)
import           Ledger                     (Block, Blockchain, Slot (..), Tx (..), TxId, txId)
import qualified Ledger.Index               as Index
import qualified Ledger.Interval            as Interval

-- | Events produced by the blockchain emulator.
data ChainEvent =
    TxnValidate TxId
    -- ^ A transaction has been validated and added to the blockchain.
    | TxnValidationFail TxId Index.ValidationError
    -- ^ A transaction failed  to validate.
    | SlotAdd Slot
    deriving stock (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty ChainEvent where
    pretty = \case
        TxnValidate t -> "TxnValidate" <+> pretty t
        TxnValidationFail t e -> "TxnValidationFail" <+> pretty t <> colon <+> pretty e
        SlotAdd sl -> "SlotAdd" <+> pretty sl

-- | A pool of transactions which have yet to be validated.
type TxPool = [Tx]

data ChainState = ChainState {
    _chainNewestFirst :: Blockchain, -- ^ The current chain, with the newest transactions first in the list.
    _txPool           :: TxPool, -- ^ The pool of pending transactions.
    _index            :: Index.UtxoIndex, -- ^ The UTxO index, used for validation.
    _currentSlot      :: Slot -- ^ The current slot number
} deriving (Show)

emptyChainState :: ChainState
emptyChainState = ChainState [] [] mempty 0

makeLenses ''ChainState

data ChainEffect r where
    ProcessBlock :: ChainEffect Block
    QueueTx :: Tx -> ChainEffect ()

processBlock :: Member ChainEffect effs => Eff effs Block
processBlock = send ProcessBlock

queueTx :: Member ChainEffect effs => Tx -> Eff effs ()
queueTx tx = send (QueueTx tx)

type ChainEffs = '[State ChainState, Writer [ChainEvent]]

handleChain :: (Members ChainEffs effs) => Eff (ChainEffect ': effs) ~> Eff effs
handleChain = interpret $ \case
    ProcessBlock -> do
        st <- get
        let pool  = st ^. txPool
            slot  = st ^. currentSlot
            idx   = st ^. index
            (ValidatedBlock block events rest, idx') =
                validateBlock slot idx pool

        let st' = st & txPool .~ rest
                   & chainNewestFirst %~ (block :)
                   & index .~ idx'
                   & currentSlot +~ 1 -- This assumes that there is exactly one block per slot. In the real chain there may be more than one block per slot.
        put st'
        tell events

        pure block
    QueueTx tx -> modify $ over txPool (tx :)

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
            flip S.runState idx $ for eligibleTxns $ \t -> do
                r <- validateEm slot t
                pure (t, r)

        -- The new block contains all transaction that were validated
        -- successfully
        block = fst <$> filter (isNothing . snd) processed

        -- Also return an `EmulatorEvent` for each transaction that was
        -- processed
        nextSlot = Slot (s + 1)
        events   = (reverse (uncurry mkValidationEvent <$> processed)) ++ [SlotAdd nextSlot]

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
validateEm :: S.MonadState Index.UtxoIndex m => Slot -> Tx -> m (Maybe Index.ValidationError)
validateEm h txn = do
    idx <- S.get
    let result = Index.runValidation (Index.validateTransaction h txn) idx
    case result of
        Left e -> pure (Just e)
        Right idx' -> do
            _ <- S.put idx'
            pure Nothing

makePrisms ''ChainEvent
