module Wallet where

import Types

import Bootstrap (btn, btnSecondary, btnSmall, card, cardBody_, cardTitle_, card_, col4_, pullRight, row)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Lens (view)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), br_, button, div, div_, h2_, h3_, h4_, p_, span, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Ledger.Value.TH (Value)
import Playground.API (FunctionSchema, SimpleArgumentSchema, SimulatorWallet(..), _Fn, _FunctionSchema)
import Prelude (show, ($), (<$>), (<<<), (<>))
import ValueEditor (valueForm)
import Wallet.Emulator.Types (Wallet)

walletsPane ::
  forall p.
  Signatures
  -> Value
  -> Array SimulatorWallet
  -> HTML p Query
walletsPane signatures initialValue simulatorWallets =
  div_
    [ h2_ [ text "Wallets" ]
    , p_ [ text "Add some initial wallets, then click one of your function calls inside the wallet to begin a chain of actions." ]
    , Keyed.div
        [ class_ row ]
        (Array.snoc (mapWithIndex (walletPane signatures initialValue) simulatorWallets) addWalletPane)
    ]

walletPane ::
  forall p.
  Signatures
  -> Value
  -> Int
  -> SimulatorWallet
  -> Tuple String (HTML p Query)
walletPane
  signatures
  initialValue
  walletIndex
  simulatorWallet@(SimulatorWallet { simulatorWalletWallet: wallet
                                   , simulatorWalletBalance: balance
                                   })
  =
  Tuple (show walletIndex) $
    col4_
      [ div [ classes [ ClassName "wallet", ClassName ("wallet-" <> show walletIndex) ] ]
          [ card_
              [ cardBody_
                  [ button
                      [ classes [ btn, pullRight ]
                      , onClick $ input_ $ ModifyWallets $ RemoveWallet walletIndex
                      ]
                      [ icon Close ]
                  , cardTitle_ [ h3_ [ walletIdPane wallet ] ]
                  , h4_ [ text "Opening Balances" ]
                  , valueForm (ModifyWallets <<< ModifyBalance walletIndex) balance
                  , br_
                  , h4_ [ text "Available functions" ]
                  , div_
                      (actionButton initialValue simulatorWallet <$> signatures)
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
                , onClick $ input_ $ ModifyWallets AddWallet
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
  Value
  -> SimulatorWallet
  -> FunctionSchema SimpleArgumentSchema
  -> HTML p Query
actionButton initialValue simulatorWallet functionSchema =
  button
    [ classes [ btn, btnSecondary, btnSmall, ClassName "action-button" ]
    , onClick $ input_ $ ModifyActions $ AddAction $
        Action
          { functionSchema: toArgumentLevel initialValue functionSchema
          , simulatorWallet
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
