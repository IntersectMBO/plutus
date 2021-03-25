module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Halogen.HTML (HTML, a, button, div, div_, footer, header, hr, img, input, label, main, p, text)
import Halogen.HTML.Events.Extra (onClick_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), disabled, for, href, id_, list, placeholder, readOnly, src, type_, value)
import Logo (marloweRunLogo)
import MainFrame.Lenses (_card)
import Material.Icons (Icon(..), icon_)
import Pickup.Types (Action(..), Card(..), State)
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_contractInstanceId, _contractInstanceIdString, _remoteDataWallet, _walletNickname, _walletNicknameString)
import WalletData.Types (NewWalletDetails, WalletDetails, WalletLibrary)
import WalletData.Validation (contractInstanceIdError, walletNicknameError)
import WalletData.View (nicknamesDataList)

renderPickupState :: forall p. WalletLibrary -> NewWalletDetails -> State -> HTML p Action
renderPickupState wallets newWalletDetails pickupState =
  let
    card = view _card pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative" ] ]
          [ renderPickupCard wallets newWalletDetails card
          , renderPickupScreen wallets
          ]
      ]

------------------------------------------------------------
renderPickupCard :: forall p. WalletLibrary -> NewWalletDetails -> Maybe Card -> HTML p Action
renderPickupCard wallets newWalletDetails card =
  -- TODO: currently there is only one card rendered at any time, with different content
  -- depending on the card selected in the state; we should change it so that all the
  -- cards are rendered, with at most one visible at any time (likewise in Play.State).
  -- The snag here is that some cards (like the `PickupWalletCard` below) take arguments
  -- from the current card, so we will either need to remodel or use placeholders.
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
                PickupNewWalletCard -> [ pickupNewWalletCard wallets newWalletDetails ]
                PickupWalletCard walletDetails -> [ pickupWalletCard walletDetails ]
        ]
    ]

pickupNewWalletCard :: forall p. WalletLibrary -> NewWalletDetails -> HTML p Action
pickupNewWalletCard wallets newWalletDetails =
  let
    walletNicknameString = view _walletNicknameString newWalletDetails

    contractInstanceIdString = view _contractInstanceIdString newWalletDetails

    remoteDataWallet = view _remoteDataWallet newWalletDetails

    mWalletNicknameError = walletNicknameError walletNicknameString wallets

    mContractInstanceIdError = contractInstanceIdError contractInstanceIdString remoteDataWallet wallets
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "font-bold", "mb-4" ] ]
          [ text "Demo wallet generated" ]
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
              , disabled $ isJust mWalletNicknameError || isJust mContractInstanceIdError
              , onClick_ PickupNewWallet
              ]
              [ text "Pickup" ]
          ]
      ]

pickupWalletCard :: forall p. WalletDetails -> HTML p Action
pickupWalletCard walletDetails =
  let
    nickname = view _walletNickname walletDetails

    contractId = view _contractInstanceId walletDetails
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
              , value "" -- TODO convert $ view _contractInstanceId walletDetails to string
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
        [ classNames [ "flex", "justify-between" ] ]
        [ link "Docs" ""
        , link "Marketplace" ""
        ]
    ]

pickupWalletScreen :: forall p. WalletLibrary -> HTML p Action
pickupWalletScreen wallets =
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
