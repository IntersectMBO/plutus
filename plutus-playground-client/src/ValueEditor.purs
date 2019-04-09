module ValueEditor where

import Prelude hiding (div)

import Bootstrap (btn, btnInfo, btnLink, col1_, col_, formControl, formGroup, formRow_)
import Data.Array (mapWithIndex)
import Data.Int as Int
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen (HTML)
import Halogen.HTML (ClassName(..), button, div, div_, input)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick, onValueInput)
import Halogen.HTML.Properties (InputType(..), classes, placeholder, required, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Ledger.Extra (LedgerMap(..))
import Ledger.Value.TH (CurrencySymbol(CurrencySymbol), Value(..))
import Types (ValueEvent(RemoveBalance, SetBalance, AddBalance))

valueForm :: forall p i. (ValueEvent -> HQ.Action i) -> Value -> HTML p i
valueForm handler (Value { getValue: LedgerMap balances }) =
  div_ [ Keyed.div_
           (mapWithIndex (balanceRow handler) balances)
       , button
           [ classes [ btn, btnInfo ]
           , onClick $ input_ $ handler $ AddBalance
           ]
           [ icon Plus ]
       ]

balanceRow ::
  forall p i.
  (ValueEvent -> HQ.Action i)
  -> Int
  -> Tuple CurrencySymbol Int
  -> Tuple String (HTML p i)
balanceRow handler balanceIndex balances =
  show balanceIndex
  /\
  div
    [ classes [ formGroup
              , ClassName "balance"
              , ClassName ("balance-" <> show balanceIndex)
              ]
    ]
    [ formRow_ $
        balanceForm (handler <<< SetBalance balanceIndex ) balances
        <>
        [ col1_
            [ button
                [ classes [ btn, btnLink ]
                , onClick $ input_ $ handler $ RemoveBalance balanceIndex
                ]
                [ icon Trash ]
            ]
        ]
    ]

balanceForm :: forall p i. (Tuple CurrencySymbol Int -> HQ.Action i) -> Tuple CurrencySymbol Int -> Array (HTML p i)
balanceForm handler (CurrencySymbol { unCurrencySymbol: currency } /\ amount) =
  [ col_ [
      input
        [ type_ InputNumber
        , classes [ formControl, ClassName "balance-currency-symbol" ]
        , value currency
        , required true
        , placeholder "Currency"
        , onValueInput $ \str -> do
            pure $ HQ.action $ handler $ Tuple (CurrencySymbol { unCurrencySymbol: str }) amount
        ]
    ]
  , col_ [
      input
        [ type_ InputNumber
        , classes [ formControl, ClassName "balance-amount" ]
        , value $ show amount
        , required true
        , placeholder "Amount"
        , onValueInput $ \str -> do
            newAmount <- Int.fromString str
            pure $ HQ.action $ handler $ Tuple (CurrencySymbol { unCurrencySymbol: currency }) newAmount
        ]
    ]
  ]
