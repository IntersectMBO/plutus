module Ledger.ExtraTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Lens (preview, set)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Ledger.Extra (LedgerMap(..))
import Ledger.Value.TH (CurrencySymbol(..), TokenName(TokenName))
import Node.FS (FS)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import TestUtils (equalGShow)

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Ledger.Extra" do
    indexTests
    atTests

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency"}

usd :: TokenName
usd = TokenName { unTokenName: "USD"}

eur :: TokenName
eur = TokenName { unTokenName: "EUR"}

baseValue :: LedgerMap CurrencySymbol (LedgerMap TokenName Int)
baseValue = LedgerMap [ Tuple currencies (LedgerMap [ Tuple usd 10 ]) ]

indexTests :: forall eff. TestSuite eff
indexTests =
  suite "Index" do
    test "simple gets" do
      equal (Just 10) (preview (ix currencies <<< ix usd) baseValue)
      equal Nothing   (preview (ix currencies <<< ix eur) baseValue)
    test "simple sets" do
      equal (Just 20) (baseValue
                       # set (ix currencies <<< ix usd) 20
                       # preview (ix currencies <<< ix usd)
                      )
atTests :: forall eff. TestSuite eff
atTests =
  suite "At" do
    test "create" do
      equalGShow
        baseValue
        (LedgerMap []
         # set (at currencies) (Just (LedgerMap []))
         # set (ix currencies <<< at usd) (Just 10))
    test "modify" do
      equal (Just 20) (baseValue
                       # set (ix currencies <<< at usd) (Just 20)
                       # preview (ix currencies <<< ix usd))
    test "delete" do
      equal Nothing   (baseValue
                       # set (ix currencies <<< at usd) Nothing
                       # preview (ix currencies <<< ix usd))
