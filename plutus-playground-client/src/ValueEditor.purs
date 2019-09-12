module ValueEditor where

import Prelude hiding (div, min)

import Bootstrap (col, colFormLabel, col_, formControl, formGroup, formRow_)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Int as Int
import Data.Lens (view)
import Data.Tuple (Tuple(..), fst)
import Data.Tuple.Nested ((/\))
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), div, input, label, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onValueInput)
import Halogen.HTML.Properties (InputType(InputNumber), classes, min, placeholder, required, type_, value)
import Halogen.Query as HQ
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Value (CurrencySymbol, TokenName, Value(Value))
import Types (ValueEvent(SetBalance), _currencySymbol, _tokenName)

valueForm :: forall p i. (ValueEvent -> HQ.Action i) -> Value -> HTML p i
valueForm handler (Value { getValue: balances }) =
  Keyed.div_
    (Array.concat (mapWithIndex (currencyRow handler) (Array.sortWith fst $ AssocMap.toTuples balances)))

currencyRow ::
  forall p i.
  (ValueEvent -> HQ.Action i) ->
  Int ->
  Tuple CurrencySymbol (AssocMap.Map TokenName Int) ->
  Array (Tuple String (HTML p i))
currencyRow handler currencyIndex (Tuple currencySymbol tokenBalances) = mapWithIndex (balanceRow handler currencyIndex currencySymbol) (Array.sortWith fst $ AssocMap.toTuples tokenBalances)

balanceRow ::
  forall p i.
  (ValueEvent -> HQ.Action i) ->
  Int ->
  CurrencySymbol ->
  Int ->
  Tuple TokenName Int ->
  Tuple String (HTML p i)
balanceRow handler currencyIndex currencySymbol tokenIndex (Tuple tokenName amount) =
  (show currencyIndex <> "-" <> show tokenIndex)
    /\ div
        [ classes
            [ formGroup
            , ClassName "balance"
            , ClassName ("balance-" <> show currencyIndex <> show tokenIndex)
            ]
        ]
        [ formRow_
            $ [ label
                  [ classes [ col, colFormLabel ] ]
                  [ text
                      $ case view _currencySymbol currencySymbol, view _tokenName tokenName of
                          "", "" -> "Ada"
                          _, other -> other
                  ]
              , col_
                  [ input
                      [ type_ InputNumber
                      , classes [ formControl, ClassName "balance-amount" ]
                      , value $ show amount
                      , required true
                      , placeholder "Amount"
                      , min zero
                      , onValueInput
                          $ \str -> do
                              newAmount <- Int.fromString str
                              pure $ HQ.action $ handler $ SetBalance currencySymbol tokenName newAmount
                      ]
                  ]
              ]
        ]
