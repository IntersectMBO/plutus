module ChainTests
  ( all
  ) where

import Prelude
import Chain (extractAmount)
import Data.Array (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (SimulatorWallet(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Wallet.Emulator.Wallet (Wallet(..))

all :: TestSuite
all =
  suite "Chain" do
    extractAmountsTests

extractAmountsTests :: TestSuite
extractAmountsTests =
  suite "extractAmount" do
    test "All present"
      $ equal [ Just 10, Just 40, Just 70 ]
          (map (extractAmount (currencies /\ usdToken)) wallets)
    test "All missing"
      $ equal [ Nothing, Nothing, Nothing ]
          (map (extractAmount (currencies /\ adaToken)) wallets)
    test "Mixed" do
      equal [ Just 20, Just 50, Nothing ]
        (map (extractAmount (currencies /\ eurToken)) wallets)
      equal [ Nothing, Just 30, Just 60 ]
        (map (extractAmount (ada /\ adaToken)) wallets)

wallets :: Array SimulatorWallet
wallets =
  mapWithIndex
    ( \id value ->
        SimulatorWallet
          { simulatorWalletWallet: Wallet { getWallet: id }
          , simulatorWalletBalance: value
          }
    )
    values

values :: Array Value
values =
  [ Value
      { getValue:
        AssocMap.fromTuples
          [ currencies
              /\ AssocMap.fromTuples
                  [ usdToken /\ 10
                  , eurToken /\ 20
                  ]
          ]
      }
  , Value
      { getValue:
        AssocMap.fromTuples
          [ ada /\ AssocMap.fromTuples [ adaToken /\ 30 ]
          , currencies
              /\ AssocMap.fromTuples
                  [ usdToken /\ 40
                  , eurToken /\ 50
                  ]
          ]
      }
  , Value
      { getValue:
        AssocMap.fromTuples
          [ ada /\ AssocMap.fromTuples [ adaToken /\ 60 ]
          , currencies
              /\ AssocMap.fromTuples
                  [ usdToken /\ 70
                  ]
          ]
      }
  ]

ada :: CurrencySymbol
ada = CurrencySymbol { unCurrencySymbol: "" }

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency" }

adaToken :: TokenName
adaToken = TokenName { unTokenName: "" }

usdToken :: TokenName
usdToken = TokenName { unTokenName: "USDToken" }

eurToken :: TokenName
eurToken = TokenName { unTokenName: "EURToken" }
