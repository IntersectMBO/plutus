module Language.PlutusTx.AssocMapTests
  ( all
  ) where

import Prelude
import Data.Lens (preview, set)
import Data.Lens.At (at)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Language.PlutusTx.AssocMap (Map(..), fromTuples, unionWith)
import Ledger.Extra (sum)
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import TestUtils (equalGenericShow)

all :: TestSuite
all =
  suite "Language.PlutusTx.AssocMap" do
    indexTests
    atTests
    unionWithTests
    unionWithCurrenciesTests
    sumTests

currencies :: CurrencySymbol
currencies = CurrencySymbol { unCurrencySymbol: "Currency" }

usd :: TokenName
usd = TokenName { unTokenName: "USD" }

eur :: TokenName
eur = TokenName { unTokenName: "EUR" }

gbp :: TokenName
gbp = TokenName { unTokenName: "GBP" }

baseValue :: Map CurrencySymbol (Map TokenName Int)
baseValue = Map [ wrap $ Tuple currencies (Map [ wrap $ Tuple usd 10 ]) ]

indexTests :: TestSuite
indexTests =
  suite "Index" do
    test "simple gets" do
      equal (Just 10) (preview (ix currencies <<< ix usd) baseValue)
      equal Nothing (preview (ix currencies <<< ix eur) baseValue)
    test "simple sets" do
      equal (Just 20)
        ( baseValue
            # set (ix currencies <<< ix usd) 20
            # preview (ix currencies <<< ix usd)
        )

atTests :: TestSuite
atTests =
  suite "At" do
    test "create" do
      equalGenericShow
        baseValue
        ( Map []
            # set (at currencies) (Just (Map []))
            # set (ix currencies <<< at usd) (Just 10)
        )
    test "modify" do
      equal (Just 20)
        ( baseValue
            # set (ix currencies <<< at usd) (Just 20)
            # preview (ix currencies <<< ix usd)
        )
    test "delete" do
      equal Nothing
        ( baseValue
            # set (ix currencies <<< at usd) Nothing
            # preview (ix currencies <<< ix usd)
        )

unionWithTests :: TestSuite
unionWithTests = do
  suite "unionWith" do
    let
      a =
        fromTuples
          [ "a" /\ 1
          , "b" /\ 2
          , "c" /\ 3
          ]
    let
      b =
        fromTuples
          [ "b" /\ 1
          , "c" /\ 2
          , "d" /\ 3
          ]
    test "Merge with (+)" do
      equal
        ( fromTuples
            [ "a" /\ 1
            , "b" /\ 3
            , "c" /\ 5
            , "d" /\ 3
            ]
        )
        (unionWith (+) a b)
    test "Merge with (-)" do
      equal
        ( fromTuples
            [ "a" /\ 1
            , "b" /\ 1
            , "c" /\ 1
            , "d" /\ 3
            ]
        )
        (unionWith (-) a b)

unionWithCurrenciesTests :: TestSuite
unionWithCurrenciesTests =
  suite "unionWith - currencies" do
    let
      valueA =
        ( Map
            [ wrap
                $ Tuple currencies
                    ( Map
                        [ wrap $ Tuple usd 10
                        , wrap $ Tuple eur 20
                        ]
                    )
            ]
        )

      valueB =
        ( Map
            [ wrap
                $ Tuple currencies
                    ( Map
                        [ wrap $ Tuple eur 30
                        , wrap $ Tuple gbp 40
                        ]
                    )
            ]
        )
    test "addition"
      $ equalGenericShow
          ( Map
              [ wrap
                  $ Tuple currencies
                      ( Map
                          [ wrap $ Tuple usd 10
                          , wrap $ Tuple eur 50
                          , wrap $ Tuple gbp 40
                          ]
                      )
              ]
          )
          (unionWith (unionWith (+)) valueA valueB)
    test "choice"
      $ equalGenericShow
          ( Map
              [ wrap
                  $ Tuple currencies
                      ( Map
                          [ wrap $ Tuple usd 10
                          , wrap $ Tuple eur 20
                          , wrap $ Tuple gbp 40
                          ]
                      )
              ]
          )
          (unionWith (unionWith const) valueA valueB)

sumTests :: TestSuite
sumTests =
  suite "sum" do
    let
      valueA =
        ( Map
            [ wrap
                $ Tuple currencies
                    ( Map
                        [ wrap $ Tuple usd 10
                        , wrap $ Tuple eur 20
                        ]
                    )
            ]
        )

      valueB =
        ( Map
            [ wrap
                $ Tuple currencies
                    ( Map
                        [ wrap $ Tuple eur 30
                        , wrap $ Tuple gbp 40
                        ]
                    )
            ]
        )
    test "sum"
      $ equalGenericShow
          ( Value
              { getValue:
                ( Map
                    [ wrap
                        $ Tuple currencies
                            ( Map
                                [ wrap $ Tuple usd 10
                                , wrap $ Tuple eur 50
                                , wrap $ Tuple gbp 40
                                ]
                            )
                    ]
                )
              }
          )
          (sum (Value { getValue: valueA }) (Value { getValue: valueB }))
