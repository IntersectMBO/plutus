module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Newtype (unwrap)
import Data.UUID (toString) as UUID
import Halogen.HTML (HTML, a, button, div, div_, footer, header, hr, img, input, label, main, p, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, src, type_, value)
import Logo (marloweRunLogo)
import MainFrame.Lenses (_card)
import Material.Icons (Icon(..), icon_)
import Pickup.Lenses (_pickingUp, _pickupWalletString)
import Pickup.Types (Action(..), Card(..), PickupNewWalletContext(..), State)
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_contractInstanceId, _contractInstanceIdString, _remoteDataWalletInfo, _walletNickname, _walletNicknameString)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletLibrary)
import WalletData.Validation (contractInstanceIdError, walletNicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. WalletLibrary -> NewWalletDetails -> State -> HTML p Action
renderPickupState wallets newWalletDetails pickupState =
  let
    card = view _card pickupState

    pickingUp = view _pickingUp pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative" ] ]
          -- In the Play view, there are potentially many cards all inside a containing div,
          -- and the last one has a semi-transparent overlay (using class "last:bg-overlay").
          -- Here in the Pickup view there is at most one card, but we need to put it inside
          -- a containing div as well, so that it's the last child, and has the bg-overlay
          -- applied.
          [ div_ [ renderPickupCard wallets newWalletDetails card pickingUp ]
          , renderPickupScreen wallets pickupState
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. WalletLibrary -> NewWalletDetails -> Maybe Card -> Boolean -> HTML p Action
renderPickupCard wallets newWalletDetails card pickingUp =
  div
    [ classNames $ Css.overlay $ isNothing card ]
    [ div
        [ classNames $ Css.card $ isNothing card ]
        [ a
            [ classNames [ "absolute", "top-4", "right-4" ]
            , onClick_ $ SetCard Nothing
            ]
            [ icon_ Close ]
        , div_
            $ (flip foldMap card) \cardType -> case cardType of
                PickupNewWalletCard pickupNewWalletContext -> [ pickupNewWalletCard wallets newWalletDetails pickingUp pickupNewWalletContext ]
                PickupWalletCard walletDetails -> [ pickupWalletCard pickingUp walletDetails ]
        ]
    ]

pickupNewWalletCard :: forall p. WalletLibrary -> NewWalletDetails -> Boolean -> PickupNewWalletContext -> HTML p Action
pickupNewWalletCard wallets newWalletDetails pickingUp pickupNewWalletContext =
  let
    walletNicknameString = view _walletNicknameString newWalletDetails

    contractInstanceIdString = view _contractInstanceIdString newWalletDetails

    remoteDataWalletInfo = view _remoteDataWalletInfo newWalletDetails

    mWalletNicknameError = walletNicknameError walletNicknameString wallets

    mContractInstanceIdError = contractInstanceIdError contractInstanceIdString remoteDataWalletInfo wallets
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-bold", "mb-4" ] ]
          [ text $ "Demo wallet "
              <> case pickupNewWalletContext of
                  WalletGenerated -> "generated"
                  WalletFound -> "found"
          ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
          $ [ label
                [ classNames $ Css.nestedLabel
                , for "newWalletNickname"
                ]
                [ text "Nickname" ]
            , input
                $ [ type_ InputText
                  , classNames $ (Css.input $ isJust mWalletNicknameError) <> [ "text-lg" ]
                  , id_ "newWalletNickname"
                  , placeholder "Nickname"
                  , value walletNicknameString
                  , onValueInput_ SetNewWalletNickname
                  ]
            , div
                [ classNames Css.inputError ]
                [ text $ foldMap show mWalletNicknameError ]
            ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "newWalletKey"
              ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ (Css.input false) <> [ "text-lg" ]
              , id_ "newWalletKey"
              , value contractInstanceIdString
              , readOnly true
              ]
          , div
              [ classNames Css.inputError ]
              [ text $ foldMap show mContractInstanceIdError ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , disabled $ isJust mWalletNicknameError || isJust mContractInstanceIdError || pickingUp
              , onClick_ PickupNewWallet
              ]
              [ text if pickingUp then "Picking up... " else "Pickup" ]
          ]
      ]

pickupWalletCard :: forall p. Boolean -> WalletDetails -> HTML p Action
pickupWalletCard pickingUp walletDetails =
  let
    nickname = view _walletNickname walletDetails

    contractInstanceId = view _contractInstanceId walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-bold", "mb-4" ] ]
          [ text $ "Play wallet " <> nickname ]
      , div
          [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
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
          [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
          [ label
              [ classNames Css.nestedLabel
              , for "walletId"
              ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input false
              , id_ "walletId"
              , value $ UUID.toString $ unwrap contractInstanceId
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ SetCard Nothing
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ $ PickupWallet walletDetails
              , disabled pickingUp
              ]
              [ text if pickingUp then "Picking up... " else "Pickup" ]
          ]
      ]

------------------------------------------------------------
renderPickupScreen :: forall p. Warn (Text "We need to add the Marlowe links.") => WalletLibrary -> State -> HTML p Action
renderPickupScreen wallets pickupState =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "flex" ] ]
        [ link "marlowe.io" "" ]
    , pickupWalletScreen wallets pickupState
    , footer
        [ classNames [ "flex", "justify-between" ] ]
        [ link "Docs" ""
        , link "Marketplace" ""
        ]
    ]

pickupWalletScreen :: forall p. WalletLibrary -> State -> HTML p Action
pickupWalletScreen wallets pickupState =
  let
    pickupWalletString = view _pickupWalletString pickupState
  in
    main
      [ classNames [ "p-4", "max-w-sm", "mx-auto", "text-center" ] ]
      [ img
          [ classNames [ "w-4/5", "mx-auto", "mb-6" ]
          , src marloweRunLogo
          ]
      , p
          [ classNames [ "mb-4" ] ]
          [ text "To use Marlowe Run, generate a new demo wallet." ]
      , button
          [ classNames $ Css.primaryButton <> [ "w-full", "text-center", "mb-4" ]
          , onClick_ GenerateNewWallet
          ]
          [ text "Generate demo wallet" ]
      , hr [ classNames [ "mb-4", "max-w-xs", "mx-auto" ] ]
      , p
          [ classNames [ "mb-4" ] ]
          [ text "Or use an existing one by selecting from the list or typing a public key or nickname." ]
      , input
          [ type_ InputText
          , classNames $ Css.inputCard false
          , id_ "existingWallet"
          , list "walletNicknames"
          , placeholder "Choose or input key/nickname"
          , value pickupWalletString
          , onValueInput_ SetPickupWalletString
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
