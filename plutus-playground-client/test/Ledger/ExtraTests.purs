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
import Ledger.Extra (LedgerMap(..), unionWith)
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
    unionWithTests

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency"}

usd :: TokenName
usd = TokenName { unTokenName: "USD"}

eur :: TokenName
eur = TokenName { unTokenName: "EUR"}

gbp :: TokenName
gbp = TokenName { unTokenName: "GBP"}

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

unionWithTests :: forall eff. TestSuite eff
unionWithTests =
  suite "unionWith" do
    let
      valueA = (LedgerMap [ Tuple currencies (LedgerMap [ Tuple usd 10
                                                        , Tuple eur 20
                                                        ]) ])
      valueB = (LedgerMap [ Tuple currencies (LedgerMap [ Tuple eur 30
                                                        , Tuple gbp 40
                                                        ]) ])
    test "addition" $
      equalGShow
        (LedgerMap [ Tuple currencies (LedgerMap [ Tuple usd 10
                                                 , Tuple eur 50
                                                 , Tuple gbp 40
                                                 ]) ])
        (unionWith (unionWith (+)) valueA valueB)
    test "choice" $
      equalGShow
        (LedgerMap [ Tuple currencies (LedgerMap [ Tuple usd 10
                                                 , Tuple eur 20
                                                 , Tuple gbp 40
                                                 ]) ])
        (unionWith (unionWith const) valueA valueB)
