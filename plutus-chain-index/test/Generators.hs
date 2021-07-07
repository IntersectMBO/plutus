{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NumericUnderscores   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-| Hedgehog generators for types used in plutus-chain-index
-}
module Generators(
    genTxOutRef,
    genRandomTxId,
    genSlot,
    genBlockId,
    -- * Stateful generator for UTXO modifications
    genTxUtxoBalance,
    genTx,
    genNonEmptyBlock,
    evalUtxoGenState
    ) where

import           Codec.Serialise             (serialise)
import           Control.Lens                (makeLenses, over, view)
import           Control.Monad               (replicateM)
import           Control.Monad.Freer         (Eff, LastMember, Member, runM, sendM, type (~>))
import           Control.Monad.Freer.State   (State, evalState, gets, modify)
import qualified Data.ByteString.Lazy        as BSL
import           Data.Set                    (Set)
import qualified Data.Set                    as Set
import           Hedgehog                    (MonadGen)
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range
import qualified Ledger.Ada                  as Ada
import           Ledger.Address              (pubKeyAddress)
import qualified Ledger.Interval             as Interval
import           Ledger.Slot                 (Slot (..))
import           Ledger.Tx                   (Address, TxIn (..), TxOut (..), TxOutRef (..))
import           Ledger.TxId                 (TxId (..))
import           Ledger.Value                (Value)
import           Plutus.ChainIndex.Tx        (ChainIndexTx (..))
import           Plutus.ChainIndex.Types     (BlockId (..), Tip (..))
import           Plutus.ChainIndex.UtxoState (TxUtxoBalance (..), fromTx)

-- | Generate a random tx id
genRandomTxId :: MonadGen m => m TxId
genRandomTxId = TxId <$> Gen.bytes (Range.singleton 32)

-- | Generate one of a known set of tx IDs
genKnownTxId :: MonadGen m => m TxId
genKnownTxId = Gen.element (txIdFromInt <$> [(1::Int)..50])

txIdFromInt :: Int -> TxId
txIdFromInt = TxId . BSL.toStrict . serialise

-- | Generate a tx id, using a known tx id in 80% of cases and a random one
--   in 20%.
genTxId :: MonadGen m => m TxId
genTxId = Gen.frequency [(8, genKnownTxId), (2, genRandomTxId)]

-- | Generate a random 'TxOutRef'
genTxOutRef :: MonadGen m => m TxOutRef
genTxOutRef =  TxOutRef <$> genTxId <*> Gen.integral (Range.linear 0 50)

genBlockId :: MonadGen m => m BlockId
genBlockId = BlockId <$> Gen.bytes (Range.singleton 32)

genSlot :: MonadGen m => m Slot
genSlot = Slot <$> Gen.integral (Range.linear 0 100000000)

-- | Generate a public key address
genAddress :: MonadGen m => m Address
genAddress = Gen.element $ pubKeyAddress <$> ["000fff", "aabbcc", "123123"]

-- | Generate a positive Ada value
genNonZeroAdaValue :: MonadGen m => m Value
genNonZeroAdaValue = Ada.lovelaceValueOf <$> Gen.integral (Range.linear 1 100_000_000_000)

-- | State of the TxOutRef generator.
data UtxoGenState =
        UtxoGenState
            { _uxUtxoSet         :: Set TxOutRef
            , _uxNumTransactions :: Int
            , _uxNumBlocks       :: Int
            }

makeLenses ''UtxoGenState

genStateTip :: UtxoGenState -> Tip
genStateTip UtxoGenState{_uxUtxoSet, _uxNumTransactions, _uxNumBlocks} =
    Tip
        { tipSlot    = fromIntegral _uxNumBlocks
        , tipBlockId = BlockId $ BSL.toStrict $ serialise _uxNumBlocks -- TODO: Incl. hash of utxo set!
        , tipBlockNo = _uxNumBlocks
        }

initialState :: UtxoGenState
initialState = UtxoGenState mempty 0 0

data ChainAction = AddTx | DoNothing

genChainAction :: MonadGen m => m ChainAction
genChainAction = Gen.frequency [(6, pure AddTx), (4, pure DoNothing)]

nextTxId :: forall effs. Member (State UtxoGenState) effs => Eff effs TxId
nextTxId = do
    -- TODO: Hash of utxo set
    lastIdx <- gets (view uxNumTransactions)
    let newId = txIdFromInt lastIdx
    modify (over uxNumTransactions succ)
    pure newId

availableInputs :: forall effs. Member (State UtxoGenState) effs => Eff effs [TxOutRef]
availableInputs = gets (Set.toList . view uxUtxoSet)

deleteInputs :: forall effs. Member (State UtxoGenState) effs => Set TxOutRef -> Eff effs ()
deleteInputs spent = modify (over uxUtxoSet (\s -> s `Set.difference` spent))

-- | Generate a valid 'Tx' that spends some UTXOs and creates some new ones
genTx ::
    forall m effs.
    ( Member (State UtxoGenState) effs
    , LastMember m effs
    , MonadGen m
    )
    => Eff effs ChainIndexTx
genTx = do
    newOutputs <-
        let outputGen = (,) <$> genAddress <*> genNonZeroAdaValue in
        sendM (Gen.list (Range.linear 1 50) outputGen)
    inputs <- availableInputs

    allInputs <-
        case inputs of
            [] -> pure []
            _  -> do
                -- To avoid generating transactions with 0 inputs
                -- we select one particular input with 'Gen.element'
                -- and then use 'Gen.subsequence' for the rest
                firstInput <- sendM (Gen.element inputs)
                otherInputs <- sendM (Gen.subsequence inputs)
                pure (firstInput : otherInputs)

    deleteInputs (Set.fromList allInputs)
    ChainIndexTx
        <$> nextTxId
        <*> pure (Set.fromList $ fmap (flip TxIn Nothing) allInputs)
        <*> pure ((\(addr, vl) -> TxOut addr vl Nothing) <$> newOutputs)
        <*> pure Interval.always

        -- TODO: generate datums, scripts, etc.
        <*> pure mempty
        <*> pure mempty
        <*> pure mempty
        <*> pure mempty

-- | Generate a 'TxUtxoBalance' based on the state of utxo changes produced so
--   far. Ensures that tx outputs are created before they are spent, and that
--   tx IDs are unique.
genTxUtxoBalance ::
    forall m effs.
    ( Member (State UtxoGenState) effs
    , LastMember m effs
    , MonadGen m
    ) => Eff effs TxUtxoBalance
genTxUtxoBalance = sendM genChainAction >>= \case
    DoNothing -> pure mempty
    AddTx     -> fromTx <$> genTx

genNonEmptyBlock ::
    forall m effs.
    ( Member (State UtxoGenState) effs
    , LastMember m effs
    , MonadGen m
    )
    => Eff effs (Tip, [ChainIndexTx])
genNonEmptyBlock = do
    numTxns <- sendM $ Gen.integral (Range.linear 1 20)
    theBlock <- replicateM numTxns genTx
    modify (over uxNumBlocks succ)
    tp <- gets genStateTip
    pure (tp, theBlock)

evalUtxoGenState :: forall m. Monad m => Eff '[State UtxoGenState, m] ~> m
evalUtxoGenState = runM . evalState initialState
