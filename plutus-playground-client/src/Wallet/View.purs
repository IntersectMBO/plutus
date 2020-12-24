module Wallet.View
  ( walletsPane
  , walletIdPane
  ) where

import Types
import Bootstrap (btn, btnSecondary, btnSmall, card, cardBody_, cardTitle_, floatRight)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Halogen.HTML (ClassName(ClassName), HTML, br_, button, div, div_, h2_, h3_, h4_, p_, span, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Ledger.Value (Value)
import Playground.Lenses (_endpointDescription, _getEndpointDescription)
import Playground.Types (ContractCall(..), FunctionSchema, SimulatorWallet(..), _FunctionSchema)
import Prelude (const, show, ($), (<$>), (<<<))
import Schema (FormSchema)
import Schema.Types (ActionEvent(..), SimulationAction(..), Signatures, toArgument)
import ValueEditor (valueForm)
import Wallet.Emulator.Wallet (Wallet)

walletClass :: ClassName
walletClass = ClassName "wallet"

actionButtonClass :: ClassName
actionButtonClass = ClassName "action-button"

actionButtonTextClass :: ClassName
actionButtonTextClass = ClassName "action-button-text"

actionButtonIconClass :: ClassName
actionButtonIconClass = ClassName "action-button-icon"

walletsPane ::
  forall p.
  Signatures ->
  Value ->
  Array SimulatorWallet ->
  HTML p HAction
walletsPane signatures initialValue simulatorWallets =
  div
    [ class_ $ ClassName "wallets" ]
    [ h2_ [ text "Wallets" ]
    , p_ [ text "Add some initial wallets, then click one of your function calls inside the wallet to begin a chain of actions." ]
    , Keyed.div
        [ class_ $ ClassName "wallet-list" ]
        (Array.snoc (mapWithIndex (walletPane signatures initialValue) simulatorWallets) addWalletPane)
    ]

walletPane ::
  forall p.
  Signatures ->
  Value ->
  Int ->
  SimulatorWallet ->
  Tuple String (HTML p HAction)
walletPane signatures initialValue walletIndex simulatorWallet@( SimulatorWallet
    { simulatorWalletWallet: wallet
  , simulatorWalletBalance: balance
  }
) =
  Tuple (show walletIndex)
    $ div
        [ classes [ card, walletClass ] ]
        [ cardBody_
            [ button
                [ classes [ btn, floatRight, ClassName "close-button" ]
                , onClick $ const $ Just $ ModifyWallets $ RemoveWallet walletIndex
                ]
                [ icon Close ]
            , cardTitle_ [ h3_ [ walletIdPane wallet ] ]
            , h4_ [ text "Opening Balances" ]
            , valueForm (ModifyWallets <<< ModifyBalance walletIndex) balance
            , br_
            , h4_ [ text "Available functions" ]
            , div
                [ class_ $ ClassName "available-actions" ]
                [ ChangeSimulation <$> div_ (actionButton initialValue simulatorWallet <$> signatures)
                , ChangeSimulation <$> div_ [ addPayToWalletButton initialValue simulatorWallet ]
                ]
            ]
        ]

-- this function is exported so that actions panes can show their associated wallet
walletIdPane :: forall p i. Wallet -> HTML p i
walletIdPane wallet =
  span [ class_ $ ClassName "wallet-id" ]
    [ text "Wallet "
    , text $ show $ _.getWallet $ unwrap wallet
    ]

addWalletPane :: forall p. Tuple String (HTML p HAction)
addWalletPane =
  Tuple "add-wallet"
    $ div
        [ classes [ card, walletClass, ClassName "add-wallet" ]
        , onClick $ const $ Just $ ModifyWallets AddWallet
        ]
        [ cardBody_
            [ icon Plus
            , div_ [ text "Add Wallet" ]
            ]
        ]

actionButton ::
  forall p.
  Value ->
  SimulatorWallet ->
  FunctionSchema FormSchema ->
  HTML p SimulationAction
actionButton initialValue simulatorWallet functionSchema =
  button
    [ classes [ btn, btnSecondary, btnSmall, actionButtonClass ]
    , onClick $ const $ Just $ ModifyActions $ AddAction
        $ CallEndpoint
            { argumentValues: toArgument initialValue <$> functionSchema
            , caller: view _simulatorWalletWallet simulatorWallet
            }
    ]
    [ span
        [ class_ actionButtonTextClass ]
        [ text $ view (_FunctionSchema <<< _endpointDescription <<< _getEndpointDescription) functionSchema ]
    , span
        [ class_ actionButtonIconClass ]
        [ icon Plus ]
    ]

addPayToWalletButton ::
  forall p.
  Value ->
  SimulatorWallet ->
  HTML p SimulationAction
addPayToWalletButton initialValue simulatorWallet =
  button
    [ classes [ btn, btnSecondary, btnSmall, actionButtonClass ]
    , onClick $ const $ Just $ ModifyActions $ AddAction
        $ PayToWallet
            { sender: view _simulatorWalletWallet simulatorWallet
            , recipient: view _simulatorWalletWallet simulatorWallet
            , amount: initialValue
            }
    ]
    [ span
        [ class_ actionButtonTextClass ]
        [ text "Pay to Wallet" ]
    , span
        [ class_ actionButtonIconClass ]
        [ icon Plus ]
    ]
