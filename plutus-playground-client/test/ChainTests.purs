module ChainTests
       ( all
       ) where

import Prelude

import Chain (extractAmount)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Array (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Ledger.Extra (LedgerMap(..))
import Ledger.Value.TH (CurrencySymbol(..), TokenName(..), Value(..))
import Node.FS (FS)
import Playground.API (SimulatorWallet(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Wallet.Emulator.Types (Wallet(..))


all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Chain" do
    extractAmountsTests

extractAmountsTests :: forall eff. TestSuite eff
extractAmountsTests =
  suite "extractAmount" do
    test "All present" $
      equal [ Just 10, Just 40, Just 70 ]
       (map (extractAmount (currencies /\ usdToken)) wallets)
    test "All missing" $
      equal [ Nothing, Nothing, Nothing ]
        (map (extractAmount (currencies /\ adaToken)) wallets)
    test "Mixed" do
      equal [ Just 20, Just 50, Nothing ]
        (map (extractAmount (currencies /\ eurToken)) wallets)
      equal [ Nothing, Just 30, Just 60 ]
        (map (extractAmount (ada /\ adaToken)) wallets)


wallets :: Array SimulatorWallet
wallets =
  mapWithIndex
    (\id value -> SimulatorWallet { simulatorWalletWallet: Wallet { getWallet: id }
                                  , simulatorWalletBalance: value
                                  })
    values

values :: Array Value
values =
  [ Value { getValue: LedgerMap [ currencies /\ LedgerMap [ usdToken /\ 10
                                                          , eurToken /\ 20
                                                          ]
                                ] }
  , Value { getValue: LedgerMap [ ada /\ LedgerMap [ adaToken /\ 30 ]
                                , currencies /\ LedgerMap [ usdToken /\ 40
                                                          , eurToken /\ 50
                                                          ]
                                ] }
  , Value { getValue: LedgerMap [ ada /\ LedgerMap [ adaToken /\ 60 ]
                                , currencies /\ LedgerMap [ usdToken /\ 70
                                                          ]
                                ] }
  ]

ada :: CurrencySymbol
ada = CurrencySymbol { unCurrencySymbol: ""}

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency"}

adaToken :: TokenName
adaToken = TokenName { unTokenName: ""}

usdToken :: TokenName
usdToken = TokenName { unTokenName: "USDToken"}

eurToken :: TokenName
eurToken = TokenName { unTokenName: "EURToken"}
