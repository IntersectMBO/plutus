module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames, hideWhen, toggleWhen)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Tuple (fst, snd)
import Halogen.HTML (HTML, a, br_, button, div, footer, h2_, header, input, label, main, p, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, type_, value)
import MainFrame.Lenses (_card, _screen)
import Material.Icons as Icon
import Pickup.Types (Action(..), Card(..), Screen(..), State)
import WalletData.Lenses (_key, _nickname)
import WalletData.Types (WalletLibrary, WalletNicknameKey)
import WalletData.Validation (nicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. WalletLibrary -> WalletNicknameKey -> State -> HTML p Action
renderPickupState wallets newWalletNicknameKey pickupState =
  let
    screen = view _screen pickupState

    card = view _card pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
          [ renderPickupCard card newWalletNicknameKey wallets
          , renderPickupScreen wallets screen
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. Maybe Card -> WalletNicknameKey -> WalletLibrary -> HTML p Action
renderPickupCard pickupCard newWalletNicknameKey wallets =
  div
    [ classNames $ [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen (isNothing pickupCard) ]
    [ div
        [ classNames $ [ "shadow-md", "bg-white", "mx-1", "md:mx-auto", "md:w-card" ] <> hideWhen (isNothing pickupCard) ]
        [ div
            [ classNames [ "flex", "justify-end" ] ]
            [ a
                [ classNames [ "p-0.5", "text-green" ]
                , onClick_ $ SetCard Nothing
                ]
                [ Icon.close ]
            ]
        , div
            [ classNames [ "px-1", "pb-1" ] ] case pickupCard of
            Just PickupNewWalletCard -> [ pickupNewWalletCard newWalletNicknameKey wallets ]
            Just (PickupWalletCard walletNicknameKey) -> [ pickupLocalWalletCard walletNicknameKey ]
            Nothing -> []
        ]
    ]

pickupNewWalletCard :: forall p. WalletNicknameKey -> WalletLibrary -> HTML p Action
pickupNewWalletCard newWalletNicknameKey wallets =
  let
    nickname = view _nickname newWalletNicknameKey

    key = view _key newWalletNicknameKey

    mNicknameError = nicknameError nickname wallets
  in
    div
      [ classNames [ "flex", "flex-col" ] ]
      [ h2_
          [ text "New wallet generated" ]
      , label
          [ for "newWalletKey" ]
          [ text "Key:" ]
      , input
          [ type_ InputText
          , id_ "newWalletKey"
          , value key
          , readOnly true
          ]
      , br_
      , label
          [ for "newWalletNickname" ]
          [ text "Nickname:" ]
      , input
          [ type_ InputText
          , classNames $ toggleWhen (mNicknameError == Nothing) "border-green" "border-red"
          , id_ "newWalletNickname"
          , placeholder "Nickname"
          , value nickname
          , onValueInput_ SetNewWalletNickname
          ]
      , div
          [ classNames [ "mb-1", "text-red", "text-sm" ] ]
          $ case mNicknameError of
              Just nicknameError -> [ text $ show nicknameError ]
              Nothing -> []
      , button
          [ disabled $ isJust mNicknameError
          , onClick_ PickupNewWallet
          ]
          [ text "Pickup new wallet" ]
      ]

pickupLocalWalletCard :: forall p. WalletNicknameKey -> HTML p Action
pickupLocalWalletCard walletNicknameKey =
  div
    [ classNames [ "flex", "flex-col" ] ]
    [ h2_
        [ text "Wallet found" ]
    , label
        [ for "newWalletKey" ]
        [ text "Key:" ]
    , input
        [ type_ InputText
        , id_ "newWalletKey"
        , value $ snd walletNicknameKey
        , readOnly true
        ]
    , br_
    , label
        [ for "newWalletNickname" ]
        [ text "Nickname:" ]
    , input
        [ type_ InputText
        , id_ "newWalletNickname"
        , placeholder "Nickname"
        , value $ fst walletNicknameKey
        , readOnly true
        ]
    , br_
    , button
        [ onClick_ $ PickupWallet $ snd walletNicknameKey ]
        [ text "Pickup wallet" ]
    ]

------------------------------------------------------------
renderPickupScreen :: forall p. WalletLibrary -> Screen -> HTML p Action
renderPickupScreen wallets screen = case screen of
  GenerateWalletScreen ->
    div
      [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0" ] ]
      [ pickupWalletScreen wallets ]

pickupWalletScreen :: forall p. WalletLibrary -> HTML p Action
pickupWalletScreen wallets =
  div
    [ classNames [ "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link Icon.navigateBefore "Back to marlowe.io" "" ]
    , main
        [ classNames [ "flex", "flex-col", "p-1", "max-w-md", "mx-auto" ] ]
        [ h2_
            [ text "Welcome to the Marlowe Dashboard" ]
        , p
            [ classNames [ "mb-1" ] ]
            [ text "Here be some words of wisdom." ]
        , button
            [ classNames [ "mb-1" ]
            , onClick_ GenerateNewWallet
            ]
            [ text "Generate play wallet" ]
        , label
            [ classNames [ "text-sm", "font-bold" ]
            , for "existingWallet"
            ]
            [ text "Pickup existing wallet" ]
        , input
            [ type_ InputText
            , id_ "existingWallet"
            , list "walletNicknames"
            , onValueInput_ LookupWallet
            ]
        , nicknamesDataList wallets
        ]
    , footer
        [ classNames [ "flex" ] ]
        [ link Icon.navigateNext "Docs" ""
        , link Icon.navigateNext "Library" ""
        ]
    ]
  where
  link icon label url =
    a
      [ classNames [ "flex", "items-center", "text-green", "p-0.5" ]
      , href url
      ]
      [ icon, text label ]
