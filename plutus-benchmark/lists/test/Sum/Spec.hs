-- editorconfig-checker-disable-file
module Sum.Spec (tests) where

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

import PlutusBenchmark.Common (Term, cekResultMatchesHaskellValue)

import PlutusBenchmark.Lists.Sum.Compiled qualified as Compiled
import PlutusBenchmark.Lists.Sum.HandWritten qualified as HandWritten

import PlutusTx.Test qualified as Tx

-- | Check that the various summation functions all give the same result as 'sum'

prop_sum :: ([Integer] -> Term) -> [Integer] -> Property
prop_sum termMaker l = cekResultMatchesHaskellValue (termMaker l) (===) (sum l)

tests :: TestTree
tests =
  testGroup "plutus-benchmark list-sum tests"
    [ testGroup "correct evaluation"
      [ testProperty "Handwritten right fold (Scott lists)"    $ prop_sum HandWritten.mkSumRightScottTerm
      , testProperty "Handwritten right fold (built-in lists)" $ prop_sum HandWritten.mkSumRightBuiltinTerm
      , testProperty "Compiled right fold (Scott lists)"       $ prop_sum Compiled.mkSumRightScottTerm
      , testProperty "Compiled right fold (built-in lists)"    $ prop_sum Compiled.mkSumRightBuiltinTerm
      , testProperty "Compiled right fold (data lists)"        $ prop_sum Compiled.mkSumRightDataTerm
      , testProperty "Handwritten left fold (Scott lists)"     $ prop_sum HandWritten.mkSumLeftScottTerm
      , testProperty "Handwritten left fold (built-in lists)"  $ prop_sum HandWritten.mkSumLeftBuiltinTerm
      , testProperty "Compiled left fold (Scott lists)"        $ prop_sum Compiled.mkSumLeftScottTerm
      , testProperty "Compiled left fold (built-in lists)"     $ prop_sum Compiled.mkSumLeftBuiltinTerm
      , testProperty "Compiled left fold (data lists)"         $ prop_sum Compiled.mkSumLeftDataTerm
      ]
    , runTestNestedIn ["lists", "test"] $ testNested "Sum"
      [ Tx.goldenBudget "right-fold-scott"    $ Compiled.mkSumRightScottCode input
      , Tx.goldenBudget "right-fold-built-in" $ Compiled.mkSumRightBuiltinCode input
      , Tx.goldenBudget "right-fold-data"     $ Compiled.mkSumRightDataCode input
      , Tx.goldenBudget "left-fold-scott"     $ Compiled.mkSumLeftScottCode input
      , Tx.goldenBudget "left-fold-built-in"  $ Compiled.mkSumLeftBuiltinCode input
      , Tx.goldenBudget "left-fold-data"      $ Compiled.mkSumLeftDataCode input
      ]
    ]
  where input = [1..100]
