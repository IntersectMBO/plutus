{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NumericUnderscores   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
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
    genTxOutBalance,
    genTxIdState,
    genTxState,
    genTx,
    genNonEmptyBlock,
    runTxGenState,
    evalTxGenState,
    execTxGenState,
    txgsBlocks,
    txgsUtxoSet,
    txgsStxoSet,
    txgsNumTransactions,
    genTxStateTipAndTx,
    txIdFromInt
    ) where

import           Codec.Serialise                 (serialise)
import           Control.Lens                    (makeLenses, over, view)
import           Control.Monad                   (replicateM)
import           Control.Monad.Freer             (Eff, LastMember, Member, runM, sendM, type (~>))
import           Control.Monad.Freer.State       (State, evalState, execState, gets, modify, runState)
import qualified Data.ByteString.Lazy            as BSL
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Hedgehog                        (MonadGen)
import qualified Hedgehog.Gen                    as Gen
import qualified Hedgehog.Range                  as Range
import qualified Ledger.Ada                      as Ada
import           Ledger.Address                  (pubKeyAddress)
import qualified Ledger.Generators               as Gen
import qualified Ledger.Interval                 as Interval
import           Ledger.Slot                     (Slot (..))
import           Ledger.Tx                       (Address, TxIn (..), TxOut (..), TxOutRef (..))
import           Ledger.TxId                     (TxId (..))
import           Ledger.Value                    (Value)
import qualified Ledger.Value                    as Value
import           Plutus.ChainIndex.Tx            (ChainIndexTx (..), ChainIndexTxOutputs (..), txOutRefs)
import qualified Plutus.ChainIndex.TxIdState     as TxIdState
import qualified Plutus.ChainIndex.TxOutBalance  as TxOutBalance
import qualified Plutus.ChainIndex.TxUtxoBalance as TxUtxoBalance
import           Plutus.ChainIndex.Types         (BlockId (..), BlockNumber (..), Tip (..), TxIdState, TxOutBalance,
                                                  TxUtxoBalance (..))
import qualified PlutusTx.Prelude                as PlutusTx

-- | Generate a random tx id
genRandomTxId :: MonadGen m => m TxId
genRandomTxId = TxId . PlutusTx.toBuiltin <$> Gen.bytes (Range.singleton 32)

-- | Generate one of a known set of tx IDs
genKnownTxId :: MonadGen m => m TxId
genKnownTxId = Gen.element (txIdFromInt <$> [(1::Int)..50])

txIdFromInt :: Int -> TxId
txIdFromInt = TxId . PlutusTx.toBuiltin . BSL.toStrict . serialise

-- | Generate a tx id, using a known tx id in 80% of cases and a random one
--   in 20%.
genTxId :: MonadGen m => m TxId
genTxId = Gen.frequency [(8, genKnownTxId), (2, genRandomTxId)]

-- | Generate a random 'TxOutRef'
genTxOutRef :: MonadGen m => m TxOutRef
genTxOutRef = TxOutRef <$> genTxId <*> Gen.integral (Range.linear 0 50)

genBlockId :: MonadGen m => m BlockId
genBlockId = BlockId <$> Gen.bytes (Range.singleton 32)

genSlot :: MonadGen m => m Slot
genSlot = Slot <$> Gen.integral (Range.linear 0 100000000)

-- | Generate a public key address
genAddress :: MonadGen m => m Address
genAddress = Gen.element $ pubKeyAddress <$> ["000fff", "aabbcc", "123123"]

-- | Generate random Value (possibly containing Ada) with a positive Ada value.
genNonZeroAdaValue :: MonadGen m => m Value
genNonZeroAdaValue = do
  value <- Value.singleton <$> (Value.currencySymbol <$> Gen.genSizedByteStringExact 32)
                           <*> (Value.tokenName <$> Gen.genSizedByteString 32)
                           <*> Gen.integral (Range.linear 1 100_000_000_000)
  ada <- Ada.lovelaceValueOf <$> Gen.integral (Range.linear 1 100_000_000_000)
  pure $ value <> ada

data TxGenState =
        TxGenState
            { _txgsUtxoSet         :: Set TxOutRef
            , _txgsStxoSet         :: Map TxOutRef TxId
            , _txgsBlocks          :: [[TxId]]
            , _txgsNumTransactions :: Int
            }
            deriving Show

makeLenses ''TxGenState

genStateTip :: TxGenState -> Tip
genStateTip TxGenState {_txgsBlocks, _txgsNumTransactions} =
    Tip
        { tipSlot    = Slot (fromIntegral numBlocks) -- Because in every slot we have one block.
        , tipBlockId = BlockId $ BSL.toStrict $ serialise numBlocks
        , tipBlockNo = BlockNumber (fromIntegral numBlocks)
        }
  where
    numBlocks = length _txgsBlocks

initialState :: TxGenState
initialState = TxGenState mempty mempty mempty 0

data ChainAction = AddTx | DoNothing

genChainAction :: MonadGen m => m ChainAction
genChainAction = Gen.frequency [(6, pure AddTx), (4, pure DoNothing)]

nextTxId :: forall effs. Member (State TxGenState) effs => Eff effs TxId
nextTxId = do
    -- TODO: Hash of utxo set
    lastIdx <- gets (view txgsNumTransactions)
    let newId = txIdFromInt lastIdx
    modify (over txgsNumTransactions succ)
    pure newId

availableInputs :: forall effs. Member (State TxGenState) effs => Eff effs [TxOutRef]
availableInputs = gets (Set.toList . view txgsUtxoSet)

deleteInputs
  :: forall effs. Member (State TxGenState) effs
  => Map TxOutRef TxId
  -> Eff effs ()
deleteInputs spent = do
  modify (over txgsUtxoSet (\s -> s `Set.difference` Map.keysSet spent))
  modify (over txgsStxoSet (\s -> s <> spent))

-- | Generate a valid 'Tx' that spends some UTXOs and creates some new ones
genTx ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    )
    => Eff effs ChainIndexTx
genTx = do
    newOutputs <-
        let outputGen = (,) <$> genAddress <*> genNonZeroAdaValue in
        sendM (Gen.list (Range.linear 1 5) outputGen)
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

    txId <- nextTxId

    deleteInputs (Map.fromSet (const txId) $ Set.fromList allInputs)

    tx <- pure (ChainIndexTx txId)
        <*> pure (Set.fromList $ fmap (flip TxIn Nothing) allInputs)
        <*> pure (ValidTx $ (\(addr, vl) -> TxOut addr vl Nothing) <$> newOutputs)
        <*> pure Interval.always

        -- TODO: generate datums, scripts, etc.
        <*> pure mempty
        <*> pure mempty
        <*> pure mempty

        -- TODO: We need a way to convert the generated 'ChainIndexTx' to a
        -- 'SomeCardanoTx', or vis-versa. And then put it here.
        <*> pure Nothing

    modify (over txgsBlocks ((:) [txId]))
    modify (over txgsUtxoSet ((<>) (Set.fromList $ txOutRefs tx)))
    pure tx

-- | Generate a 'TxUtxoBalance' based on the state of utxo changes produced so
--   far. Ensures that tx outputs are created before they are spent, and that
--   tx IDs are unique.
genTxUtxoBalance ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    ) => Eff effs TxUtxoBalance
genTxUtxoBalance = fmap (\(s,_,_) -> s) genTxState

genTxOutBalance ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    ) => Eff effs TxOutBalance
genTxOutBalance = fmap (\(_,s,_) -> s) genTxState

genTxIdState ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    ) => Eff effs TxIdState
genTxIdState = fmap (\(_,_,s) -> s) genTxState

genTxState ::
  forall m effs.
  ( Member (State TxGenState) effs
  , LastMember m effs
  , MonadGen m
  ) => Eff effs (TxUtxoBalance, TxOutBalance, TxIdState)
genTxState = sendM genChainAction >>= \case
    DoNothing -> pure (mempty, mempty, mempty)
    AddTx     -> do
      blockNumber <- length <$> gets (view txgsBlocks)
      tx <- genTx
      pure ( TxUtxoBalance.fromTx tx
           , TxOutBalance.fromTx tx
           , TxIdState.fromTx (BlockNumber (fromIntegral blockNumber)) tx
           )

execTxGenState :: forall m a. Monad m => Eff '[State TxGenState, m] a -> m TxGenState
execTxGenState = runM . execState initialState

evalTxGenState :: forall m. Monad m => Eff '[State TxGenState, m] ~> m
evalTxGenState = runM . evalState initialState

runTxGenState :: forall m a. Monad m => Eff '[State TxGenState, m] a -> m (a, TxGenState)
runTxGenState = runM . runState initialState

genNonEmptyBlock ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    )
    => Eff effs (Tip, [ChainIndexTx])
genNonEmptyBlock = do
    numTxns <- sendM $ Gen.integral (Range.linear 1 10)
    theBlock <- replicateM numTxns genTx
    tp <- gets genStateTip
    pure (tp, theBlock)

genTxStateTipAndTx ::
    forall m effs.
    ( Member (State TxGenState) effs
    , LastMember m effs
    , MonadGen m
    )
    => Eff effs (Tip, ChainIndexTx)
genTxStateTipAndTx  = do
  chainIndexTx <- genTx
  tip <- gets genStateTip
  pure (tip, chainIndexTx)
