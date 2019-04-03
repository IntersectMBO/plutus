module Ledger.ExtraTests
       ( all
       ) where

import Prelude

import Data.Lens (_1, over, traversed)
import Ledger.Extra (Value(..))
import Data.Tuple (Tuple(..))
import Ledger.Map.TH (Map(..))
import Ledger.Value.TH (CurrencySymbol(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)

all :: forall eff. TestSuite eff
all =
  suite "Ledger.Extra" do
    valueTests

valueTests :: forall eff. TestSuite eff
valueTests = do
  test "eq" do
    equal
      (toValue [ Tuple 1 100, Tuple 2 0 ])
      (toValue [ Tuple 1 100 ])
    equal
      (toValue [ Tuple 1 100, Tuple 2 5 ])
      (toValue [ Tuple 2 5, Tuple 1 100 ])

  where
    toValue xs =
      Value {getValue: Map {unMap: (over (traversed <<< _1) CurrencySymbol xs)}}
