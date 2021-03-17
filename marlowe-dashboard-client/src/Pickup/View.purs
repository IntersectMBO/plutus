module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Halogen.HTML (HTML, a, button, div, div_, footer, h1, header, hr, input, label, main, p, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, type_, value)
import MainFrame.Lenses (_card)
import Marlowe.Semantics (PubKey)
import Material.Icons (Icon(..), icon_)
import Network.RemoteData (RemoteData)
import Pickup.Types (Action(..), Card(..), State)
import Prim.TypeError (class Warn, Text)
import Servant.PureScript.Ajax (AjaxError)
import WalletData.Lenses (_contractId, _nickname)
import WalletData.Types (Nickname, WalletDetails, WalletLibrary)
import WalletData.Validation (contractIdError, nicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> State -> HTML p Action
renderPickupState wallets newWalletNickname newWalletContractId remoteDataPubKey pickupState =
  let
    card = view _card pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative" ] ]
          [ renderPickupCard wallets newWalletNickname newWalletContractId remoteDataPubKey card
          , renderPickupScreen wallets
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> Maybe Card -> HTML p Action
renderPickupCard wallets newWalletNickname newWalletContractId remoteDataPubKey card =
  div
    [ classNames $ Css.overlay $ isNothing card ]
    [ div
        [ classNames Css.cardWrapper ]
        [ div
            [ classNames $ Css.card $ isNothing card ]
            [ div
                [ classNames [ "flex", "justify-end", "-m-3", "mb-3", "sticky", "top-0" ] ]
                [ a
                    [ onClick_ $ SetCard Nothing ]
                    [ icon_ Close ]
                ]
            , div_
                $ (flip foldMap card) \cardType -> case cardType of
                    PickupNewWalletCard -> [ pickupNewWalletCard wallets newWalletNickname newWalletContractId remoteDataPubKey ]
                    PickupWalletCard walletDetails -> [ pickupWalletCard walletDetails ]
            ]
        ]
    ]

pickupNewWalletCard :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> HTML p Action
pickupNewWalletCard wallets newWalletNickname newWalletContractId remoteDataPubKey =
  let
    mNicknameError = nicknameError newWalletNickname wallets

    mContractIdError = contractIdError newWalletContractId remoteDataPubKey wallets
  in
    div_
      [ p
          [ classNames [ "font-bold", "mb-3" ] ]
          [ text "Demo wallet generated" ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-3" ] ]
          $ [ label
                [ classNames $ Css.nestedLabel
                , for "newWalletNickname"
                ]
                [ text "Nickname" ]
            , input
                $ [ type_ InputText
                  , classNames $ (Css.input $ isJust mNicknameError) <> [ "text-lg" ]
                  , id_ "newWalletNickname"
                  , placeholder "Nickname"
                  , value newWalletNickname
                  , onValueInput_ SetNewWalletNickname
                  ]
            , div
                [ classNames Css.inputError ]
                [ text $ foldMap show mNicknameError ]
            ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-3" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "newWalletKey"
              ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ (Css.input false) <> [ "text-lg" ]
              , id_ "newWalletKey"
              , value newWalletContractId
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-3" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mNicknameError || isJust mContractIdError
              , onClick_ PickupNewWallet
              ]
              [ text "Pickup" ]
          ]
      ]

pickupWalletCard :: forall p. WalletDetails -> HTML p Action
pickupWalletCard walletDetails =
  let
    nickname = view _nickname walletDetails

    contractId = view _contractId walletDetails
  in
    div_
      [ p
          [ classNames [ "font-bold", "mb-3" ] ]
          [ text $ "Play wallet " <> nickname ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-3" ] ]
          $ [ label
                [ classNames $ Css.nestedLabel
                , for "nickname"
                ]
                [ text "Nickname" ]
            , input
                $ [ type_ InputText
                  , classNames $ Css.input false
                  , id_ "nickname"
                  , value nickname
                  , readOnly true
                  ]
            ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-3" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "walletId"
              ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false
              , id_ "walletId"
              , value $ view _contractId walletDetails
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-3" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ $ PickupWallet walletDetails
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
    [ classNames [ "p-3", "max-w-sm", "mx-auto", "text-center" ] ]
    [ h1
        [ classNames [ "text-3xl", "font-bold", "mb-3" ] ]
        [ text "Marlowe" ]
    , p
        [ classNames [ "mb-3" ] ]
        [ text "To use Marlowe Run, generate a new demo wallet." ]
    , button
        [ classNames $ Css.primaryButton <> [ "w-full", "text-center", "mb-3" ]
        , onClick_ GenerateNewWallet
        ]
        [ text "Generate demo wallet" ]
    , hr [ classNames [ "mb-3", "max-w-xs", "mx-auto" ] ]
    , p
        [ classNames [ "mb-3" ] ]
        [ text "Or use an existing one by selecting from the list or typing a public key or nickname." ]
    , input
        [ type_ InputText
        , classNames $ Css.inputCard false
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
    [ classNames [ "flex", "items-center", "p-2", "font-bold" ]
    , href url
    ]
    [ text label ]
