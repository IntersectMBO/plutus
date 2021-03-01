module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Halogen.HTML (HTML, a, button, div, div_, footer, h1, header, hr_, input, label, main, p, span_, text)
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
          [ classNames [ "relative" ] ]
          [ renderPickupCard card newWalletNicknameKey wallets
          , renderPickupScreen wallets screen
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. Maybe Card -> WalletNicknameKey -> WalletLibrary -> HTML p Action
renderPickupCard pickupCard newWalletNicknameKey wallets =
  div
    [ classNames $ Css.cardWrapper $ isNothing pickupCard ]
    [ div
        [ classNames $ Css.card ]
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
            Just PickupNewWalletCard -> [ pickupWalletCard newWalletNicknameKey wallets true ]
            Just (PickupWalletCard walletNicknameKey) -> [ pickupWalletCard walletNicknameKey wallets false ]
            Nothing -> []
        ]
    ]

pickupWalletCard :: forall p. WalletNicknameKey -> WalletLibrary -> Boolean -> HTML p Action
pickupWalletCard newWalletNicknameKey wallets new =
  let
    nickname = view _nickname newWalletNicknameKey

    key = view _key newWalletNicknameKey

    mNicknameError = nicknameError nickname wallets
  in
    div_
      [ p
          [ classNames [ "font-bold", "mb-1" ] ]
          [ text if new then "Play wallet generated" else "Play wallet " <> nickname ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-1" ] ]
          $ [ label
                [ classNames $ Css.nestedLabel
                , for "newWalletNickname"
                ]
                [ text "Nickname" ]
            , input
                $ [ type_ InputText
                  , classNames $ Css.input $ if new then isJust mNicknameError else false
                  , id_ "newWalletNickname"
                  , placeholder "Nickname"
                  , value nickname
                  ]
                <> if new then [ onValueInput_ SetNewWalletNickname ] else [ readOnly true ]
            ]
          <> if new then
              [ div
                  [ classNames Css.inputError ]
                  $ case mNicknameError of
                      Just nicknameError -> [ text $ show nicknameError ]
                      Nothing -> []
              ]
            else
              []
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-1" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "newWalletKey"
              ]
              [ text "Public key" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false
              , id_ "newWalletKey"
              , value key
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-1" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ if new then isJust mNicknameError else false
              , onClick_ if new then PickupNewWallet else PickupWallet key
              ]
              [ text "Pickup" ]
          ]
      ]

------------------------------------------------------------
renderPickupScreen :: forall p. WalletLibrary -> Screen -> HTML p Action
renderPickupScreen wallets screen =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link Icon.navigateBefore "Back to marlowe.io" "" ]
    , case screen of
        GDPRScreen -> gdprScreen
        GenerateWalletScreen -> pickupWalletScreen wallets
    , footer
        [ classNames [ "flex" ] ]
        [ link Icon.navigateNext "Docs" ""
        , link Icon.navigateNext "Library" ""
        ]
    ]

gdprScreen :: forall p. HTML p Action
gdprScreen =
  main
    [ classNames [ "p-1", "w-22", "mx-auto", "text-center" ] ]
    [ p
        [ classNames [ "mb-1" ] ]
        [ text "Welcome to" ]
    , h1
        [ classNames [ "text-2xl", "font-bold", "mb-1" ] ]
        [ text "Marlowe" ]
    , p
        [ classNames [ "mb-1" ] ]
        [ text "GDPR text - Tiramisu toffee gingerbread lemon drops jelly cake lemon drops" ]
    , button
        [ classNames $ Css.primaryButton <> [ "w-12", "mx-auto", "justify-between" ]
        , onClick_ $ SetScreen GenerateWalletScreen
        ]
        [ span_
            [ text "I Agree" ]
        , span_
            [ Icon.navigateNext ]
        ]
    ]

pickupWalletScreen :: forall p. WalletLibrary -> HTML p Action
pickupWalletScreen wallets =
  main
    [ classNames [ "p-1", "w-22", "mx-auto", "text-center" ] ]
    [ h1
        [ classNames [ "text-2xl", "font-bold", "mb-1" ] ]
        [ text "Marlowe" ]
    , p
        [ classNames [ "mb-1" ] ]
        [ text "To use the Marlowe demo, generate a new wallet." ]
    , button
        [ classNames $ Css.primaryButton <> [ "w-full", "mb-1" ]
        , onClick_ GenerateNewWallet
        ]
        [ text "Generate play wallet" ]
    , hr_
    , p
        [ classNames [ "mb-1" ] ]
        [ text "Or pickup an existing one by selecting from the list or typing a public key or nickname." ]
    , input
        [ type_ InputText
        , classNames $ Css.input false <> [ "w-full" ]
        , id_ "existingWallet"
        , list "walletNicknames"
        , placeholder "Chose or input key/nickname"
        , onValueInput_ LookupWallet
        ]
    , nicknamesDataList wallets
    ]

link :: forall p a. HTML p a -> String -> String -> HTML p a
link icon label url =
  a
    [ classNames [ "flex", "items-center", "p-0.5" ]
    , href url
    ]
    [ icon, text label ]
