{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main(main) where

import           Control.Lens
import           Control.Monad                            (foldM, forM_, join, replicateM)
import           Control.Monad.Freer                      (Eff, Member, runM, sendM)
import           Control.Monad.Freer.Error                (Error, runError, throwError)
import           Data.Bifunctor                           (Bifunctor (..))
import           Data.Either                              (isRight)
import qualified Data.FingerTree                          as FT
import           Data.Foldable                            (fold, toList)
import           Data.List                                (nub, sort)
import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set
import qualified Generators                               as Gen
import           Hedgehog                                 (Property, annotateShow, assert, failure, forAll, property,
                                                           (/==), (===))
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range
import           Ledger                                   (TxOutRef (TxOutRef, txOutRefId))
import qualified Plutus.ChainIndex.Emulator.DiskStateSpec as DiskStateSpec
import qualified Plutus.ChainIndex.Emulator.HandlersSpec  as EmulatorHandlersSpec
import qualified Plutus.ChainIndex.HandlersSpec           as HandlersSpec
import           Plutus.ChainIndex.Tx                     (citxTxId)
import           Plutus.ChainIndex.TxIdState              (dropOlder, increaseDepth, transactionStatus)
import qualified Plutus.ChainIndex.TxIdState              as TxIdState
import qualified Plutus.ChainIndex.TxOutBalance           as TxOutBalance
import qualified Plutus.ChainIndex.TxUtxoBalance          as TUB
import           Plutus.ChainIndex.Types                  (BlockNumber (..), Depth (..), RollbackState (..), Tip (..),
                                                           TxConfirmedState (..), TxIdState (..), TxOutState (..),
                                                           TxStatusFailure (..), TxUtxoBalance (..), TxValidity (..),
                                                           liftTxOutStatus, tipAsPoint, txOutStatusTxOutState)
import           Plutus.ChainIndex.UtxoState              (InsertUtxoSuccess (..), RollbackResult (..))
import qualified Plutus.ChainIndex.UtxoState              as UtxoState
import           Test.Tasty
import           Test.Tasty.Hedgehog                      (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "tests"
    [ testGroup "tx out balance" txOutBalanceTests
    , testGroup "utxo balance" utxoBalanceTests
    , testGroup "txidstate" txIdStateTests
    , testProperty "lift tx output status to tx status" txOutStatusTxStatusProp
    , testProperty "tx output status" txOutStatusSpentUnspentProp
    , DiskStateSpec.tests
    , EmulatorHandlersSpec.tests
    , HandlersSpec.tests
    ]

utxoBalanceTests :: [TestTree]
utxoBalanceTests =
  [ testGroup "monoid"
      [ testProperty "associative" semigroupUtxobalanceAssociative
      , testProperty "unit" monoidUtxobalanceUnit
      ]
  , testGroup "generator"
      [ testProperty "match all unspent outputs" matchUnspentOutputs
      , testProperty "generate block with non-empty utxo set"
                     generateBlockWithNonEmptyTxUtxoBalance
      ]
  , testGroup "operations"
      [ testProperty "insert new blocks at end" insertAtEnd
      , testProperty "rollback" rollback
      , testProperty "block number ascending order" blockNumberAscending
      , testProperty "reduce block count" reduceBlockCount
      ]
  ]

txOutBalanceTests :: [TestTree]
txOutBalanceTests =
  [ testGroup "monoid"
      [ testProperty "associative" semigroupTxOutbalanceAssociative
      , testProperty "unit" monoidTxOutbalanceUnit
      ]
  , testGroup "generator"
      [ testProperty "generate non-empty blocks" generateBlocksWithNonEmptyTxOutBalance
      ]
  ]

txIdStateTests :: [TestTree]
txIdStateTests =
  [ testGroup "monoid"
      [ testProperty "associative" semigroupTxIdStateAssociative
      , testProperty "unit" monoidTxIdStateUnit
      ]
  , testGroup "generator"
      [ testProperty "unique transaction ids" uniqueTransactionIds
      , testProperty "number of transactions = number of blocks" numOfTransactionsIsNumberOfBlocks
      ]
  , testGroup "operations"
      [ testProperty "transaction depth increases" transactionDepthIncreases
      , testProperty "rollback changes tx state" rollbackTxIdState
      , testProperty "dropOlder drops only older things." dropOlderDropsCorrectly
      ]
  ]

dropOlderDropsCorrectly :: Property
dropOlderDropsCorrectly = property $ do
  ((tipA, txA), (tipB, txB)) <- forAll $ Gen.evalTxGenState
                       $ (,)
                      <$> Gen.genTxStateTipAndTx
                      <*> Gen.genTxStateTipAndTx


  let Right s1 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 1) txA) tipA) mempty
      f1 = newIndex s1

      Right s2 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 2) txB) tipB) f1
      f2 = newIndex s2

      Right s2' = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 2) txB) tipB) mempty
      f2' = newIndex s2'

  -- The present one isn't dropped.
  f1 === dropOlder (BlockNumber 1) f1

  -- But it's dropped next time, if we advanced one step.
  mempty === dropOlder (BlockNumber 2) f1

  -- Then, it only contains one thing if we drop off the first state.
  f2' === dropOlder (BlockNumber 2) f2

rollbackTxIdState :: Property
rollbackTxIdState = property $ do
  ((tipA, txA), (tipB, txB)) <- forAll $ Gen.evalTxGenState
                      $ (,)
                      <$> Gen.genTxStateTipAndTx
                      <*> Gen.genTxStateTipAndTx

  let getState = UtxoState._usTxUtxoData . UtxoState.utxoState

      Right s1 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 0) txA) tipA) mempty
      f1 = newIndex s1

      Right s2 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 1) txB) tipB) f1
      f2 = newIndex s2

      Right s3 = TxIdState.rollback (tipAsPoint tipA) f2
      f3 = rolledBackIndex s3

      -- Add it back again.
      Right s4 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 2) txB) tipB) f3
      f4 = newIndex s4

  let confirmed tx txIdState = timesConfirmed <$> ( Map.lookup (tx ^. citxTxId) $ txnsConfirmed $ getState txIdState)
      deleted tx txIdState = Map.lookup (tx ^. citxTxId) $ txnsDeleted $ getState txIdState
      status bn tx txIdState = transactionStatus (BlockNumber bn) (getState txIdState) (tx ^. citxTxId)

      isInvalidRollback (Left InvalidRollbackAttempt {}) = True
      isInvalidRollback _                                = False

  -- It's inserted at f2, and is confirmed once and not deleted, resulting
  -- in a tentatively-confirmed status.
  confirmed txB f2 === Just 1
  deleted txB f2   === Nothing
  status 1 txB f2  === (Right $ TentativelyConfirmed (Depth 0) TxValid ())

  -- At f3, it's deleted once, and confirmed once, resulting in an unknown
  -- status.
  confirmed txB f3 === Just 1
  deleted txB f3   === Just 1
  status 2 txB f3  === Right Unknown

  -- If we check the status far into the future, this should be an error, as
  -- we're trying to rollback something that is committed.
  isInvalidRollback (status 100 txB f3) === True

  -- At f4, it's confirmed twice, and deleted once, resulting in a
  -- tentatively-confirmed status again.
  confirmed txB f4 === Just 2
  deleted txB f4   === Just 1
  status 3 txB f4  === (Right $ TentativelyConfirmed (Depth 1) TxValid ())

  -- Much later, it should be committed.
  status 100 txB f4 === Right (Committed TxValid ())

transactionDepthIncreases :: Property
transactionDepthIncreases = property $ do
  ((tipA, txA), (tipB, txB)) <- forAll
                                 $ Gen.evalTxGenState
                                 $ (,) <$> Gen.genTxStateTipAndTx <*> Gen.genTxStateTipAndTx

  let Depth d = TxIdState.chainConstant
      Right s1 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 0) txA) tipA) mempty
      Right s2 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 1) txB) tipB) f1
      f1 = newIndex s1
      f2 = newIndex s2

  let status1 = transactionStatus (BlockNumber 0) (UtxoState._usTxUtxoData (UtxoState.utxoState f1)) (txA ^. citxTxId)
      status2 = transactionStatus (BlockNumber 1) (UtxoState._usTxUtxoData (UtxoState.utxoState f2)) (txA ^. citxTxId)
      status3 = transactionStatus (BlockNumber (1 + fromIntegral d)) (UtxoState._usTxUtxoData (UtxoState.utxoState f2)) (txA ^. citxTxId)

  status2 === (increaseDepth <$> status1)
  status3 === (Right $ Committed TxValid ())

uniqueTransactionIds :: Property
uniqueTransactionIds = property $ do
  a <- forAll $ Gen.execTxGenState Gen.genTxState
  let txIds = join (a ^. Gen.txgsBlocks)
  txIds === nub txIds

numOfTransactionsIsNumberOfBlocks :: Property
numOfTransactionsIsNumberOfBlocks = property $ do
  a <- forAll $ Gen.execTxGenState Gen.genTxState
  let numTransactionsInBlocks = length $ join (a ^. Gen.txgsBlocks)
      transactionCount    = a ^. Gen.txgsNumTransactions
  numTransactionsInBlocks === transactionCount

semigroupTxIdStateAssociative :: Property
semigroupTxIdStateAssociative = property $ do
    (a, b, c) <- forAll $ Gen.evalTxGenState $ (,,) <$> Gen.genTxState <*> Gen.genTxState <*> Gen.genTxState
    a <> (b <> c) === (a <> b) <> c

monoidTxIdStateUnit :: Property
monoidTxIdStateUnit = property $ do
    a <- forAll $ Gen.evalTxGenState Gen.genTxState
    a <> mempty === a
    mempty <> a === a

semigroupUtxobalanceAssociative :: Property
semigroupUtxobalanceAssociative = property $ do
    (a, b, c) <- forAll $ Gen.evalTxGenState $ (,,) <$> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance
    a <> (b <> c) === (a <> b) <> c

monoidUtxobalanceUnit :: Property
monoidUtxobalanceUnit = property $ do
    a <- forAll $ Gen.evalTxGenState Gen.genTxUtxoBalance
    a <> mempty === a
    mempty <> a === a

matchUnspentOutputs :: Property
matchUnspentOutputs = property $ do
    n <- forAll $ Gen.integral (Range.linear 0 1000)
    items <- forAll $ Gen.evalTxGenState $ replicateM n Gen.genTxUtxoBalance
    -- when we have caught up with the chain, all spent inputs should be matched
    -- (this is more of a test of the generator)
    _tubUnmatchedSpentInputs (fold items) === Set.empty

generateBlockWithNonEmptyTxUtxoBalance :: Property
generateBlockWithNonEmptyTxUtxoBalance = property $ do
    block <- forAll $ Gen.evalTxGenState Gen.genNonEmptyBlock
    assert $ not $ Set.null $ TUB.unspentOutputs (uncurry TUB.fromBlock block)

generateBlocksWithNonEmptyTxOutBalance :: Property
generateBlocksWithNonEmptyTxOutBalance = property $ do
    blocks <- forAll $ Gen.evalTxGenState $ replicateM 2 Gen.genNonEmptyBlock
    let state = foldMap (uncurry TxOutBalance.fromBlock) blocks
    assert $ not $ Set.null $ TxOutBalance.unspentOutputs state
    assert $ not $ Set.null $ TxOutBalance.spentOutputs state

insertAtEnd :: Property
insertAtEnd = property $ do
    numBlocks <- forAll $ Gen.integral (Range.linear 0 500)
    blocks <- forAll $ Gen.evalTxGenState $ replicateM numBlocks Gen.genNonEmptyBlock
    let result =
          foldM
             (\InsertUtxoSuccess{newIndex} (tip, txns) -> UtxoState.insert (TUB.fromBlock tip txns) newIndex)
             InsertUtxoSuccess{newIndex=mempty, insertPosition=UtxoState.InsertAtEnd}
             blocks
    case result of
        Left _                                  -> failure
        Right InsertUtxoSuccess{insertPosition} -> insertPosition === UtxoState.InsertAtEnd

liftError :: forall e a effs. Member (Error e) effs => Either e a -> Eff effs a
liftError = either throwError pure

type RollbackErr = Either UtxoState.InsertUtxoFailed UtxoState.RollbackFailed

liftInsert :: forall a effs. Member (Error RollbackErr) effs => Either UtxoState.InsertUtxoFailed a -> Eff effs a
liftInsert = liftError @RollbackErr . first Left

liftRollback :: forall a effs. Member (Error RollbackErr) effs => Either UtxoState.RollbackFailed a -> Eff effs a
liftRollback = liftError @RollbackErr . first Right

-- | Rolling back to an old tip gives the same utxo set as we
--   had at that tip.
rollback :: Property
rollback = property $ do
    (block1, block2, block3, block4) <- forAll $ Gen.evalTxGenState $ (,,,) <$> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock
    result <- runM $ runError @RollbackErr $ do
        InsertUtxoSuccess{newIndex=ix1} <- liftInsert $ UtxoState.insert (uncurry TUB.fromBlock block1) mempty
        sendM $ annotateShow ix1
        InsertUtxoSuccess{newIndex=ix2} <- liftInsert $ UtxoState.insert (uncurry TUB.fromBlock block2) ix1
        InsertUtxoSuccess{newIndex=ix3} <- liftInsert $ UtxoState.insert (uncurry TUB.fromBlock block3) ix2

        let tip1 = fst block1
        RollbackResult{rolledBackIndex=ix1'} <- liftRollback $ TUB.rollback (tipAsPoint tip1) ix3
        sendM $ TUB.unspentOutputs (UtxoState.utxoState ix1) === TUB.unspentOutputs (UtxoState.utxoState ix1')
        sendM $ UtxoState.tip (UtxoState.utxoState ix1') === tip1

        InsertUtxoSuccess{newIndex=ix4} <- liftInsert $ UtxoState.insert (uncurry TUB.fromBlock block4) ix1
        InsertUtxoSuccess{newIndex=ix4'} <- liftInsert $ UtxoState.insert (uncurry TUB.fromBlock block4) ix1'
        sendM $ TUB.unspentOutputs (UtxoState.utxoState ix4) === TUB.unspentOutputs (UtxoState.utxoState ix4')
        sendM $ UtxoState.tip (UtxoState.utxoState ix4') === fst block4
    annotateShow result
    assert $ isRight result

-- | The items of the finger tree are always in ascending order
--   regardless of insertion order
blockNumberAscending :: Property
blockNumberAscending = property $ do
    numBlocks <- forAll $ Gen.integral (Range.linear 0 500)
    blocks <- forAll $ Gen.evalTxGenState $ replicateM numBlocks Gen.genNonEmptyBlock
    shuffledBlocks <- forAll $ Gen.shuffle blocks
    let result = foldM
                    (\InsertUtxoSuccess{newIndex} (tip, txns) -> UtxoState.insert (TUB.fromBlock tip txns) newIndex)
                    InsertUtxoSuccess{newIndex=mempty, insertPosition=UtxoState.InsertAtEnd}
                    shuffledBlocks
    case result of
        Left e                                  -> do
            annotateShow e
            failure
        Right InsertUtxoSuccess{newIndex} -> do
            let items = tipBlockNo' . UtxoState.tip <$> toList newIndex
            items === sort items
    where
        tipBlockNo' TipAtGenesis               = error "There should be no empty UtxoState."
        tipBlockNo' (Tip _ _ (BlockNumber no)) = no

-- | Reducing the block count does not change the utxo state.
reduceBlockCount :: Property
reduceBlockCount = property $ do
    numBlocks <- forAll $ Gen.integral (Range.linear 0 500)
    blocks <- forAll $ Gen.evalTxGenState $ replicateM numBlocks Gen.genNonEmptyBlock
    let utxoIndex = foldMap (FT.singleton . uncurry TUB.fromBlock) blocks
    minCount <- forAll $ Gen.integral (Range.linear 0 numBlocks)
    case UtxoState.reduceBlockCount (Depth minCount) utxoIndex of
        UtxoState.BlockCountNotReduced -> assert $ UtxoState.utxoBlockCount utxoIndex <= minCount * 2
        UtxoState.ReduceBlockCountResult limitedIndex (UtxoState.UtxoState _ tip) -> do
            UtxoState.utxoState limitedIndex === UtxoState.utxoState utxoIndex
            UtxoState.utxoBlockCount limitedIndex === minCount + 1
            tip /== TipAtGenesis

semigroupTxOutbalanceAssociative :: Property
semigroupTxOutbalanceAssociative = property $ do
    (a, b, c) <- forAll $ Gen.evalTxGenState $ (,,) <$> Gen.genTxOutBalance <*> Gen.genTxOutBalance <*> Gen.genTxOutBalance
    a <> (b <> c) === (a <> b) <> c

monoidTxOutbalanceUnit :: Property
monoidTxOutbalanceUnit = property $ do
    a <- forAll $ Gen.evalTxGenState Gen.genTxOutBalance
    a <> mempty === a
    mempty <> a === a

-- | Given a tx output status, we can convert it to a tx status and compare it
-- with the actual tx status.
txOutStatusTxStatusProp :: Property
txOutStatusTxStatusProp = property $ do
  -- Generate a certain number of blocks
  let (Depth n) = TxIdState.chainConstant
  numBlocks <- forAll $ Gen.integral (Range.linear (n-1) (n+1))
  (txStates, txGenState) <- forAll $ Gen.runTxGenState $ replicateM numBlocks Gen.genTxState
  let txOutBalance = foldMap (\(_,s,_) -> s) txStates
  let txIdState = foldMap (\(_,_,s) -> s) txStates
  let blockNumber = BlockNumber (fromIntegral numBlocks)

  -- Combine spent and unspent outptus
  let txOutputs = view Gen.txgsUtxoSet txGenState
               <> Map.keysSet (view Gen.txgsStxoSet txGenState)

  forM_ txOutputs $ \txOutRef@TxOutRef{ txOutRefId } -> do
    let txOutStatusE =
          TxOutBalance.transactionOutputStatus blockNumber txIdState txOutBalance txOutRef
    case txOutStatusE of
      Left _ -> Hedgehog.assert True
      Right txOutStatus -> do
        case txOutStatusTxOutState txOutStatus of
          Nothing -> Hedgehog.assert True
          Just Unspent ->
            case transactionStatus blockNumber txIdState txOutRefId of
              Left _         -> Hedgehog.assert True
              Right txStatus -> txStatus === liftTxOutStatus txOutStatus
          Just (Spent txid) ->
            case transactionStatus blockNumber txIdState txid of
              Left _         -> Hedgehog.assert True
              Right txStatus -> txStatus === liftTxOutStatus txOutStatus

-- | Testing whether the state of a transaction output is correctly spend or
-- unspend.
txOutStatusSpentUnspentProp :: Property
txOutStatusSpentUnspentProp = property $ do
  -- Generate a 'c' number of blocks to make sure that the tx state is always
  -- tentatively confirmed, as testing for the state committed is out of the
  -- scope of this test.
  let (Depth c) = TxIdState.chainConstant
  (blocks, txGenState) <- forAll $ Gen.runTxGenState
                                 $ replicateM c Gen.genNonEmptyBlock

  let blockNumber = BlockNumber (fromIntegral c)
      txIdState = foldMap (\(n, txns) -> foldMap (TxIdState.fromTx n) txns)
                          $ zip [1..] $ fmap snd blocks
      txOutBalance = foldMap TxOutBalance.fromTx $ concatMap snd blocks

  -- We verify that every unspent tx output has the status
  -- 'TxOutTentativelyUnspent'.
  forM_ (view Gen.txgsUtxoSet txGenState) $ \txOutRef -> do
    let txOutStatus = TxOutBalance.transactionOutputStatus blockNumber
                                                  txIdState
                                                  txOutBalance
                                                  txOutRef
    case txOutStatus of
      Right (TentativelyConfirmed _ TxValid Unspent) -> Hedgehog.assert True
      _                                              -> Hedgehog.assert False

  -- We verify that every spent tx output has the status
  -- 'TxOutTentativelySpent'.
  forM_ (Map.toList $ view Gen.txgsStxoSet txGenState) $ \(txOutRef, txOutSpentTxId) -> do
    let txOutStatus =
          TxOutBalance.transactionOutputStatus blockNumber txIdState txOutBalance txOutRef
    case txOutStatus of
      Right (TentativelyConfirmed _ TxValid (Spent txId)) | txId == txOutSpentTxId -> Hedgehog.assert True
      _                                                                            -> Hedgehog.assert False

