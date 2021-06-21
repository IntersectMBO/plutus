
module Main(main) where

import           Control.Monad               (replicateM)
import           Data.Foldable               (fold)
import qualified Data.Set                    as Set
import qualified Generators                  as Gen
import           Hedgehog                    (Property, forAll, property, (===))
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range
import           Plutus.ChainIndex.UtxoState (TxUtxoBalance (..))
import           Test.Tasty
import           Test.Tasty.Hedgehog         (testProperty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "utxo balance" [
    testGroup "monoid" [
        testProperty "associative" semigroup_utxobalance_associative,
        testProperty "unit" monoid_utxobalance_unit
        ],
    testGroup "generator" [
        testProperty "match all unspent outputs" match_unspent_outputs
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
    tubUnmatchedSpentInputs (fold items) === Set.empty
