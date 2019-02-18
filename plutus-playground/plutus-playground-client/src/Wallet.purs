module Wallet where

import Types

import Bootstrap (btn, btnSecondary, btnSmall, card, cardBody_, cardTitle_, card_, col4_, col_, pullRight, row, row_)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Int as Int
import Data.Lens (view)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), button, div, div_, h2_, h3_, h4_, input, p_, span, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, placeholder, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Playground.API (FunctionSchema, MockWallet, SimpleArgumentSchema, _Fn, _FunctionSchema)
import Prelude (map, show, ($), (<$>), (<<<))
import Wallet.Emulator.Types (Wallet)

walletsPane ::
  forall p.
  Signatures
  -> Array MockWallet
  -> HTML p Query
walletsPane signatures mockWallets =
  div_
    [ h2_ [ text "Wallets" ]
    , p_ [ text "Add some initial wallets, then click one of your function calls inside the wallet to begin a chain of actions." ]
    , Keyed.div
        [ class_ row ]
        (Array.snoc (mapWithIndex (walletPane signatures) mockWallets) addWalletPane)
    ]

walletPane ::
  forall p.
  Signatures
  -> Int
  -> MockWallet
  -> Tuple String (HTML p Query)
walletPane signatures index mockWallet =
  Tuple (show index) $
    col4_
      [ div
          [class_ $ ClassName "wallet"]
          [ card_
              [ cardBody_
                  [ button
                      [ classes [ btn, pullRight ]
                      , onClick $ input_ $ RemoveWallet index
                      ]
                      [ icon Close ]
                  , cardTitle_ [ h3_ [ walletIdPane (view _mockWalletWallet mockWallet) ] ]
                  , row_
                      [ col_ [ text "ADA" ]
                      , col_ [
                          input
                            [ type_ InputNumber
                            , value $ show $ view _mockWalletBalance mockWallet
                            , placeholder "Int"
                            , onValueChange $ map (HQ.action <<< SetBalance (view _mockWalletWallet mockWallet)) <<< Int.fromString
                            ]
                        ]
                      ]
                  , h4_ [ text "Available functions" ]
                  , div_
                      (actionButton mockWallet <$> signatures)
                  ]
              ]
          ]
      ]

addWalletPane :: forall p. Tuple String (HTML p Query)
addWalletPane =
  Tuple "add-wallet" $
    col4_
      [ div
          [ class_ $ ClassName "add-wallet" ]
          [ div [ class_ card
                , onClick $ input_ AddWallet
                ]
              [ cardBody_
                  [ icon Plus
                  , div_ [ text "Add Wallet" ]
                  ]
              ]
          ]
      ]

actionButton ::
  forall p.
  MockWallet
  -> FunctionSchema SimpleArgumentSchema
  -> HTML p Query
actionButton mockWallet functionSchema =
  button
    [ classes [ btn, btnSecondary, btnSmall, ClassName "action-button" ]
    , onClick $ input_ $ ModifyActions $ AddAction $
        Action
          { functionSchema: toValueLevel functionSchema
          , mockWallet
          }
    ]
    [ text $ view (_FunctionSchema <<< _functionName <<< _Fn) functionSchema
    , span
        [ class_ pullRight ]
        [ icon Plus ]
    ]

walletIdPane :: forall p i. Wallet -> HTML p i
walletIdPane wallet =
  span [ class_ $ ClassName "wallet-id" ]
    [ text "Wallet #"
    , text $ show $ _.getWallet $ unwrap wallet
    ]
