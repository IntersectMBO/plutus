{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Main(main) where

import           Control.Lens
import           Control.Monad                        (foldM, join, replicateM)
import           Control.Monad.Freer                  (Eff, Member, runM, sendM)
import           Control.Monad.Freer.Error            (Error, runError, throwError)
import           Data.Bifunctor                       (Bifunctor (..))
import           Data.Either                          (isRight)
import           Data.FingerTree                      (Measured (..))
import           Data.Foldable                        (fold, toList)
import           Data.List                            (nub, sort)
import qualified Data.Set                             as Set
import qualified Generators                           as Gen
import           Hedgehog                             (Property, annotateShow, assert, failure, forAll, property, (===))
import qualified Hedgehog.Gen                         as Gen
import qualified Hedgehog.Range                       as Range
import qualified Plutus.ChainIndex.Emulator.DiskState as DiskState
import           Plutus.ChainIndex.Tx                 (citxTxId, txOutsWithRef)
import           Plutus.ChainIndex.TxIdState          (BlockNumber (..), TxStatus (..), TxValidity (..), increaseDepth,
                                                       transactionStatus)
import qualified Plutus.ChainIndex.TxIdState          as TxIdState
import           Plutus.ChainIndex.Types              (Tip (..), tipAsPoint)
import           Plutus.ChainIndex.UtxoState          (InsertUtxoSuccess (..), RollbackResult (..), TxUtxoBalance (..))
import qualified Plutus.ChainIndex.UtxoState          as UtxoState
import           Test.Tasty
import           Test.Tasty.Hedgehog                  (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup "tests"
    [ testGroup "utxo balance" utxoBalanceTests
    , testGroup "txidstate" txIdStateTests
    ]

utxoBalanceTests :: [TestTree]
utxoBalanceTests =
  [ testGroup "monoid"
      [ testProperty "associative" semigroupUtxobalanceAssociative
      , testProperty "unit" monoidUtxobalanceUnit
      ]
  , testGroup "generator"
      [ testProperty "match all unspent outputs" matchUnspentOutputs
      , testProperty "generate non-empty blocks" generateNonEmptyBlocks
      , testProperty "same txOuts between AddressMap and ChainIndexTx" addressMapAndTxShouldShareTxOuts
      ]
  , testGroup "operations"
      [ testProperty "insert new blocks at end" insertAtEnd
      , testProperty "rollback" rollback
      , testProperty "block number ascending order" blockNumberAscending
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
      , testProperty "number of transactions = number of blocks" transactionBlockNumbers
      ]
  , testGroup "operations"
      [ testProperty "transaction depth increases" transactionDepthIncreases
      , testProperty "rollback changes tx state" rollbackTxIdState
      ]
  ]

rollbackTxIdState :: Property
rollbackTxIdState = property $ do
  ((tipA, txA), (tipB, txB)) <- forAll $ Gen.evalTxIdGenState
                      $ (,)
                      <$> Gen.genTxIdStateTipAndTxId
                          <*> Gen.genTxIdStateTipAndTxId

  let getState = UtxoState._usTxUtxoData . measure

      Right s1 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 0) txA) tipA) mempty
      f1 = newIndex s1

      Right s2 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 1) txB) tipB) f1
      f2 = newIndex s2

      Right s3 = TxIdState.rollback (tipAsPoint tipA) f2
      f3 = rolledBackIndex s3

      -- Add it back again.
      Right s4 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 2) txB) tipB) f3
      f4 = newIndex s4

      status2 = transactionStatus (BlockNumber 1) (getState f2) (txB ^. citxTxId)
      status3 = transactionStatus (BlockNumber 2) (getState f3) (txB ^. citxTxId)
      status4 = transactionStatus (BlockNumber 3) (getState f4) (txB ^. citxTxId)

  status2 === TentativelyConfirmed (TxIdState.Depth 0) TxValid
  status3 === Unknown
  status4 === TentativelyConfirmed (TxIdState.Depth 1) TxValid

transactionDepthIncreases :: Property
transactionDepthIncreases = property $ do
  ((tipA, txA), (tipB, txB)) <- forAll
                                 $ Gen.evalTxIdGenState
                                 $ (,) <$> Gen.genTxIdStateTipAndTxId <*> Gen.genTxIdStateTipAndTxId

  let TxIdState.Depth d = TxIdState.chainConstant
      Right s1 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 0) txA) tipA) mempty
      Right s2 = UtxoState.insert (UtxoState.UtxoState (TxIdState.fromTx (BlockNumber 1) txB) tipB) f1
      f1 = newIndex s1
      f2 = newIndex s2

  let status1 = transactionStatus (BlockNumber 0) (UtxoState._usTxUtxoData (measure f1)) (txA ^. citxTxId)
      status2 = transactionStatus (BlockNumber 1) (UtxoState._usTxUtxoData (measure f2)) (txA ^. citxTxId)
      status3 = transactionStatus (BlockNumber (1 + d)) (UtxoState._usTxUtxoData (measure f2)) (txA ^. citxTxId)

  status2 === increaseDepth status1
  status3 === Committed TxValid

uniqueTransactionIds :: Property
uniqueTransactionIds = property $ do
  a <- forAll $ Gen.execTxIdGenState Gen.genTxIdState
  let blocks = join (a ^. Gen.txgsBlocks)
  blocks === nub blocks

transactionBlockNumbers :: Property
transactionBlockNumbers = property $ do
  a <- forAll $ Gen.execTxIdGenState Gen.genTxIdState
  let blockLengths = length $ join (a ^. Gen.txgsBlocks)
      numBlocks    = (a ^. Gen.txgsNumTransactions)
  blockLengths === numBlocks

semigroupTxIdStateAssociative :: Property
semigroupTxIdStateAssociative = property $ do
    (a, b, c) <- forAll $ Gen.evalTxIdGenState $ (,,) <$> Gen.genTxIdState <*> Gen.genTxIdState <*> Gen.genTxIdState
    a <> (b <> c) === (a <> b) <> c

monoidTxIdStateUnit :: Property
monoidTxIdStateUnit = property $ do
    a <- forAll $ Gen.evalTxIdGenState Gen.genTxIdState
    a <> mempty === a
    mempty <> a === a

semigroupUtxobalanceAssociative :: Property
semigroupUtxobalanceAssociative = property $ do
    (a, b, c) <- forAll $ Gen.evalUtxoGenState $ (,,) <$> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance
    a <> (b <> c) === (a <> b) <> c

monoidUtxobalanceUnit :: Property
monoidUtxobalanceUnit = property $ do
    a <- forAll $ Gen.evalUtxoGenState Gen.genTxUtxoBalance
    a <> mempty === a
    mempty <> a === a

matchUnspentOutputs :: Property
matchUnspentOutputs = property $ do
    n <- forAll $ Gen.integral (Range.linear 0 1000)
    items <- forAll $ Gen.evalUtxoGenState $ replicateM n Gen.genTxUtxoBalance
    -- when we have caught up with the chain, all spent inputs should be matched
    -- (this is more of a test of the generator)
    _tubUnmatchedSpentInputs (fold items) === Set.empty

-- | DiskState._AddressMap and ChainIndexTx should share the exact same set of
-- transaction outputs.
addressMapAndTxShouldShareTxOuts :: Property
addressMapAndTxShouldShareTxOuts = property $ do
    chainIndexTx <- forAll $ Gen.evalUtxoGenState Gen.genTx
    let diskState = DiskState.fromTx chainIndexTx
        chainIndexTxOutRefs = Set.fromList $ fmap snd $ txOutsWithRef chainIndexTx
        addressMapTxOutRefs =
          mconcat $ diskState ^.. DiskState.addressMap . DiskState.unCredentialMap . folded
    chainIndexTxOutRefs === addressMapTxOutRefs

generateNonEmptyBlocks :: Property
generateNonEmptyBlocks = property $ do
    block <- forAll $ Gen.evalUtxoGenState Gen.genNonEmptyBlock
    assert $ not $ Set.null $ UtxoState.unspentOutputs (uncurry UtxoState.fromBlock block)

insertAtEnd :: Property
insertAtEnd = property $ do
    numBlocks <- forAll $ Gen.integral (Range.linear 0 500)
    blocks <- forAll $ Gen.evalUtxoGenState $ replicateM numBlocks Gen.genNonEmptyBlock
    let result = foldM
                    (\InsertUtxoSuccess{newIndex} (tip, txns) -> UtxoState.insert (UtxoState.fromBlock tip txns) newIndex)
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
    (block1, block2, block3, block4) <- forAll $ Gen.evalUtxoGenState $ (,,,) <$> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock <*> Gen.genNonEmptyBlock
    result <- runM $ runError @RollbackErr $ do
        InsertUtxoSuccess{newIndex=ix1} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block1) mempty
        sendM $ annotateShow ix1
        InsertUtxoSuccess{newIndex=ix2} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block2) ix1
        InsertUtxoSuccess{newIndex=ix3} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block3) ix2

        let tip1 = fst block1
        RollbackResult{rolledBackIndex=ix1'} <- liftRollback $ UtxoState.rollback (tipAsPoint tip1) ix3
        sendM $ UtxoState.unspentOutputs (UtxoState.utxoState ix1) === UtxoState.unspentOutputs (UtxoState.utxoState ix1')
        sendM $ UtxoState.tip (UtxoState.utxoState ix1') === tip1

        InsertUtxoSuccess{newIndex=ix4} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block4) ix1
        InsertUtxoSuccess{newIndex=ix4'} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block4) ix1'
        sendM $ UtxoState.unspentOutputs (UtxoState.utxoState ix4) === UtxoState.unspentOutputs (UtxoState.utxoState ix4')
        sendM $ UtxoState.tip (UtxoState.utxoState ix4') === fst block4
    annotateShow result
    assert $ isRight result

-- | The items of the finger tree are always in ascending order
--   regardless of insertion order
blockNumberAscending :: Property
blockNumberAscending = property $ do
    numBlocks <- forAll $ Gen.integral (Range.linear 0 500)
    blocks <- forAll $ Gen.evalUtxoGenState $ replicateM numBlocks Gen.genNonEmptyBlock
    shuffledBlocks <- forAll $ Gen.shuffle blocks
    let result = foldM
                    (\InsertUtxoSuccess{newIndex} (tip, txns) -> UtxoState.insert (UtxoState.fromBlock tip txns) newIndex)
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
        tipBlockNo' :: Tip -> Int
        tipBlockNo' TipAtGenesis = error "There should be no empty UtxoState."
        tipBlockNo' (Tip _ _ no) = no
