module Wallet where

import Types
import Bootstrap (btn, btnSecondary, btnSmall, card, cardBody_, cardTitle_, card_, floatRight, responsiveThird, row)
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
import Prelude (const, show, ($), (<$>), (<<<), (<>))
import Schema (FormSchema)
import Schema.Types (ActionEvent(..), SimulationAction(..), Signatures, toArgument)
import ValueEditor (valueForm)
import Wallet.Emulator.Wallet (Wallet)

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
        [ class_ row ]
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
    $ responsiveThird
        [ div [ classes [ ClassName "wallet", ClassName ("wallet-" <> show walletIndex) ] ]
            [ card_
                [ cardBody_
                    [ button
                        [ classes [ btn, floatRight ]
                        , onClick $ const $ Just $ ModifyWallets $ RemoveWallet walletIndex
                        ]
                        [ icon Close ]
                    , cardTitle_ [ h3_ [ walletIdPane wallet ] ]
                    , h4_ [ text "Opening Balances" ]
                    , valueForm (ModifyWallets <<< ModifyBalance walletIndex) balance
                    , br_
                    , h4_ [ text "Available functions" ]
                    , ChangeSimulation <$> div_ (actionButton initialValue simulatorWallet <$> signatures)
                    , ChangeSimulation <$> div_ [ addPayToWalletButton initialValue simulatorWallet ]
                    ]
                ]
            ]
        ]

addWalletPane :: forall p. Tuple String (HTML p HAction)
addWalletPane =
  Tuple "add-wallet"
    $ responsiveThird
        [ div
            [ class_ $ ClassName "add-wallet" ]
            [ div
                [ class_ card
                , onClick $ const $ Just $ ModifyWallets AddWallet
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
    [ text $ view (_FunctionSchema <<< _endpointDescription <<< _getEndpointDescription) functionSchema
    , span
        [ class_ floatRight ]
        [ icon Plus ]
    ]

addPayToWalletButton ::
  forall p.
  Value ->
  SimulatorWallet ->
  HTML p SimulationAction
addPayToWalletButton initialValue simulatorWallet =
  button
    [ classes [ btn, btnSecondary, btnSmall, actionButtonClass, ClassName "add-pay-to-wallet-button" ]
    , onClick $ const $ Just $ ModifyActions $ AddAction
        $ PayToWallet
            { sender: view _simulatorWalletWallet simulatorWallet
            , recipient: view _simulatorWalletWallet simulatorWallet
            , amount: initialValue
            }
    ]
    [ text "Pay to Wallet"
    , span
        [ class_ floatRight ]
        [ icon Plus ]
    ]

walletIdPane :: forall p i. Wallet -> HTML p i
walletIdPane wallet =
  span [ class_ $ ClassName "wallet-id" ]
    [ text "Wallet #"
    , text $ show $ _.getWallet $ unwrap wallet
    ]

actionButtonClass :: ClassName
actionButtonClass = ClassName "action-button"
