module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Halogen.HTML (HTML, a, button, div, div_, footer, h1, header, hr_, input, label, main, p, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, type_, value)
import MainFrame.Lenses (_card)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Network.RemoteData (RemoteData)
import Pickup.Types (Action(..), Card(..), State)
import Prim.TypeError (class Warn, Text)
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Lenses (_contractId, _nickname)
import WalletData.Types (WalletDetails, WalletLibrary)
import WalletData.Validation (contractIdError, nicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> State -> HTML p Action
renderPickupState wallets newWalletDetails newWalletPubKey pickupState =
  let
    card = view _card pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative" ] ]
          [ renderPickupCard wallets newWalletDetails newWalletPubKey card
          , renderPickupScreen wallets
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> Maybe Card -> HTML p Action
renderPickupCard wallets newWalletDetails newWalletPubKey pickupCard =
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
            Just card -> [ pickupWalletCard wallets newWalletDetails newWalletPubKey card ]
            Nothing -> []
        ]
    ]

pickupWalletCard :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> Card -> HTML p Action
pickupWalletCard wallets newWalletDetails newWalletPubKey card =
  let
    nickname = view _nickname newWalletDetails

    contractId = view _contractId newWalletDetails

    mNicknameError = nicknameError nickname wallets

    mContractIdError = contractIdError contractId newWalletPubKey wallets
  in
    div_
      [ p
          [ classNames [ "font-bold", "mb-1" ] ]
          [ text
              $ case card of
                  PickupNewWalletCard -> "Play wallet generated"
                  PickupWalletCard _ -> "Play wallet " <> nickname
          ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-1" ] ]
          $ [ label
                [ classNames $ Css.nestedLabel
                , for "newWalletNickname"
                ]
                [ text "Nickname" ]
            , input
                $ [ type_ InputText
                  , classNames $ Css.input
                      $ case card of
                          PickupNewWalletCard -> isJust mNicknameError
                          PickupWalletCard _ -> false
                  , id_ "newWalletNickname"
                  , placeholder "Nickname"
                  , value nickname
                  , case card of
                      PickupNewWalletCard -> onValueInput_ SetNewWalletNickname
                      PickupWalletCard _ -> readOnly true
                  ]
            , div
                [ classNames Css.inputError ] case card of
                PickupNewWalletCard -> [ text $ foldMap show mNicknameError ]
                PickupWalletCard _ -> []
            ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-1" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "newWalletKey"
              ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false
              , id_ "newWalletKey"
              , value contractId
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
              , disabled
                  $ case card of
                      PickupNewWalletCard -> isJust mNicknameError || isJust mContractIdError
                      PickupWalletCard _ -> isJust mContractIdError
              , onClick_
                  $ case card of
                      PickupNewWalletCard -> PickupNewWallet
                      PickupWalletCard _ -> PickupWallet nickname
              ]
              [ text "Pickup" ]
          ]
      ]

------------------------------------------------------------
renderPickupScreen :: forall p. Warn (Text "We need to add the Marlowe links.") => WalletLibrary -> HTML p Action
renderPickupScreen wallets =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link "marlowe.io" "" ]
    , pickupWalletScreen wallets
    , footer
        [ classNames [ "flex" ] ]
        [ link "Docs" ""
        , link "Marketplace" ""
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

link :: forall p a. String -> String -> HTML p a
link label url =
  a
    [ classNames [ "flex", "items-center", "p-0.5" ]
    , href url
    ]
    [ text label ]
