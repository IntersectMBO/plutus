{-# LANGUAGE MonoLocalBinds   #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns   #-}
module Main(main) where

import           Control.Monad               (foldM, replicateM)
import           Control.Monad.Freer         (Eff, Member, runM, sendM)
import           Control.Monad.Freer.Error   (Error, runError, throwError)
import           Data.Bifunctor              (Bifunctor (..))
import           Data.Either                 (isRight)
import           Data.Foldable               (fold)
import qualified Data.Set                    as Set
import qualified Generators                  as Gen
import           Hedgehog                    (Property, annotateShow, assert, failure, forAll, property, (===))
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range
import           Plutus.ChainIndex.UtxoState (InsertUtxoSuccess (..), RollbackResult (..), TxUtxoBalance (..))
import qualified Plutus.ChainIndex.UtxoState as UtxoState
import           Test.Tasty
import           Test.Tasty.Hedgehog         (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
    testGroup "utxo balance" [
        testGroup "monoid" [
            testProperty "associative" semigroup_utxobalance_associative,
            testProperty "unit" monoid_utxobalance_unit
            ],
        testGroup "generator" [
            testProperty "match all unspent outputs" match_unspent_outputs,
            testProperty "generate non-empty blocks" generate_non_empty_blocks
        ],
        testGroup "operations" [
            testProperty "insert new blocks at end" insert_at_end,
            testProperty "rollback" rollback
        ]
    ]

semigroup_utxobalance_associative :: Property
semigroup_utxobalance_associative = property $ do
    (a, b, c) <- forAll $ Gen.evalUtxoGenState $ (,,) <$> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance <*> Gen.genTxUtxoBalance
    a <> (b <> c) === (a <> b) <> c

monoid_utxobalance_unit :: Property
monoid_utxobalance_unit = property $ do
    a <- forAll $ Gen.evalUtxoGenState $ Gen.genTxUtxoBalance
    a <> mempty === a
    mempty <> a === a

match_unspent_outputs :: Property
match_unspent_outputs = property $ do
    n <- forAll $ Gen.integral (Range.linear 0 1000)
    items <- forAll $ Gen.evalUtxoGenState $ replicateM n Gen.genTxUtxoBalance
    -- when we have caught up with the chain, all spent inputs should be matched
    -- (this is more of a test of the generator)
    _tubUnmatchedSpentInputs (fold items) === Set.empty

generate_non_empty_blocks :: Property
generate_non_empty_blocks = property $ do
    block <- forAll $ Gen.evalUtxoGenState Gen.genNonEmptyBlock
    assert $ not $ Set.null $ UtxoState.unspentOutputs (uncurry UtxoState.fromBlock block)

insert_at_end :: Property
insert_at_end = property $ do
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
        RollbackResult{rolledBackIndex=ix1'} <- liftRollback $ UtxoState.rollback tip1 ix3
        sendM $ UtxoState.unspentOutputs (UtxoState.utxoState ix1) === UtxoState.unspentOutputs (UtxoState.utxoState ix1')
        sendM $ UtxoState.tip (UtxoState.utxoState ix1') === Just tip1

        InsertUtxoSuccess{newIndex=ix4} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block4) ix1
        InsertUtxoSuccess{newIndex=ix4'} <- liftInsert $ UtxoState.insert (uncurry UtxoState.fromBlock block4) ix1'
        sendM $ UtxoState.unspentOutputs (UtxoState.utxoState ix4) === UtxoState.unspentOutputs (UtxoState.utxoState ix4')
        sendM $ UtxoState.tip (UtxoState.utxoState ix4') === Just (fst block4)
    annotateShow result
    assert $ isRight result
