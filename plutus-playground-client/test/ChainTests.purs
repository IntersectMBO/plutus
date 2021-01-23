module ChainTests
  ( all
  ) where

import Prelude
import Data.Array (mapWithIndex)
import Data.BigInteger as BigInteger
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Language.PlutusTx.AssocMap as AssocMap
import Plutus.V1.Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (SimulatorWallet(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Transaction.View (extractAmount)
import Wallet.Emulator.Wallet (Wallet(..))

all :: TestSuite
all =
  suite "Chain" do
    extractAmountsTests

extractAmountsTests :: TestSuite
extractAmountsTests =
  suite "extractAmount" do
    test "All present"
      $ equal
          [ Just (BigInteger.fromInt 10)
          , Just (BigInteger.fromInt 40)
          , Just (BigInteger.fromInt 70)
          ]
          (map (extractAmount (currencies /\ usdToken)) wallets)
    test "All missing"
      $ equal
          [ Nothing
          , Nothing
          , Nothing
          ]
          (map (extractAmount (currencies /\ adaToken)) wallets)
    test "Mixed" do
      equal
        [ Just (BigInteger.fromInt 20)
        , Just (BigInteger.fromInt 50)
        , Nothing
        ]
        (map (extractAmount (currencies /\ eurToken)) wallets)
      equal
        [ Nothing
        , Just (BigInteger.fromInt 30)
        , Just (BigInteger.fromInt 60)
        ]
        (map (extractAmount (ada /\ adaToken)) wallets)

wallets :: Array SimulatorWallet
wallets =
  mapWithIndex
    ( \id value ->
        SimulatorWallet
          { simulatorWalletWallet: Wallet { getWallet: BigInteger.fromInt id }
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
                    [ usdToken /\ BigInteger.fromInt 10
                    , eurToken /\ BigInteger.fromInt 20
                    ]
            ]
      }
  , Value
      { getValue:
          AssocMap.fromTuples
            [ ada /\ AssocMap.fromTuples [ adaToken /\ BigInteger.fromInt 30 ]
            , currencies
                /\ AssocMap.fromTuples
                    [ usdToken /\ BigInteger.fromInt 40
                    , eurToken /\ BigInteger.fromInt 50
                    ]
            ]
      }
  , Value
      { getValue:
          AssocMap.fromTuples
            [ ada /\ AssocMap.fromTuples [ adaToken /\ BigInteger.fromInt 60 ]
            , currencies
                /\ AssocMap.fromTuples
                    [ usdToken /\ BigInteger.fromInt 70
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
