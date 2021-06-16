module Pickup.View (renderPickupState) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.List (toUnfoldable) as List
import Data.Map (values)
import Data.Maybe (isJust, isNothing)
import Halogen.HTML (HTML, a, button, div, div_, footer, header, hr, img, label, main, p, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (disabled, for, href, src)
import Images (arrowBack, marloweRunLogo)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.View (renderInput)
import Material.Icons (Icon(..), icon, icon_)
import Network.RemoteData (isSuccess)
import Pickup.Lenses (_card, _pickingUp, _remoteWalletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput, _walletNicknameOrIdInput)
import Pickup.Types (Action(..), Card(..), State)
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_walletNickname)

renderPickupState :: forall p. State -> HTML p Action
renderPickupState state =
  div
    [ classNames [ "grid", "h-full", "relative", "overflow-x-hidden" ] ]
    [ div
        [ classNames
            $ [ "absolute", "top-0", "-left-32", "w-160", "h-32", "bg-link-highlight", "bg-cover", "opacity-10", "transform", "rotate-180" ]
            <> [ "md:-left-64", "md:w-256", "md:h-48" ]
        ]
        []
    , div
        [ classNames
            $ [ "absolute", "bottom-0", "-right-64", "w-160", "h-32", "bg-link-highlight", "bg-cover", "opacity-10" ]
            <> [ "md:w-256", "md:h-56" ]
        ]
        []
    , main
        [ classNames [ "relative" ] ]
        -- In the Play view, there are potentially many cards all inside a containing div,
        -- and the last one has a semi-transparent overlay (using class "last:bg-overlay").
        -- Here in the Pickup view there is at most one card, but we need to put it inside
        -- a containing div as well, so that it's the last child, and has the bg-overlay
        -- applied.
        [ div_ [ renderPickupCard state ]
        , renderPickupScreen state
        ]
    ]

------------------------------------------------------------
renderPickupCard :: forall p. State -> HTML p Action
renderPickupCard state =
  let
    card = view _card state
  in
    div
      [ classNames $ Css.overlay $ isNothing card ]
      [ div
          [ classNames $ Css.card $ isNothing card ]
          $ (flip foldMap card) \cardType -> case cardType of
              PickupNewWalletCard -> pickupNewWalletCard state
              PickupWalletCard -> pickupWalletCard state
              LocalWalletMissingCard -> localWalletMissingCard
      ]

pickupNewWalletCard :: forall p. State -> Array (HTML p Action)
pickupNewWalletCard state =
  let
    pickingUp = view _pickingUp state

    remoteWalletDetails = view _remoteWalletDetails state

    walletNicknameInput = view _walletNicknameInput state

    walletIdInput = view _walletIdInput state

    walletNicknameInputDisplayOptions =
      { baseCss: Css.inputCard
      , additionalCss: Css.withNestedLabel
      , id_: "walletNickname"
      , placeholder: "Choose any nickname"
      , readOnly: false
      , valueOptions: mempty
      }

    walletIdInputDisplayOptions =
      { baseCss: Css.inputCard
      , additionalCss: Css.withNestedLabel
      , id_: "walletId"
      , placeholder: "Wallet ID"
      , readOnly: true
      , valueOptions: mempty
      }
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ $ CloseCard PickupNewWalletCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
        [ p
            [ classNames [ "font-bold", "mb-4" ] ]
            [ text $ "Demo wallet generated" ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "walletNickname"
                  ]
                  [ text "Nickname" ]
              , WalletNicknameInputAction <$> renderInput walletNicknameInput walletNicknameInputDisplayOptions
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "walletID"
                ]
                [ text "Wallet ID" ]
            , WalletIdInputAction <$> renderInput walletIdInput walletIdInputDisplayOptions
            ]
        , div
            [ classNames [ "flex" ] ]
            [ button
                [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
                , onClick_ $ CloseCard PickupNewWalletCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , disabled $ isJust (validate walletNicknameInput) || pickingUp || not isSuccess remoteWalletDetails
                , onClick_ $ PickupWallet $ view _value walletNicknameInput
                ]
                [ text if pickingUp then "Picking up... " else "Pickup" ]
            ]
        ]
    ]

pickupWalletCard :: forall p. State -> Array (HTML p Action)
pickupWalletCard state =
  let
    pickingUp = view _pickingUp state

    remoteWalletDetails = view _remoteWalletDetails state

    walletNicknameInput = view _walletNicknameInput state

    walletIdInput = view _walletIdInput state

    walletNicknameInputDisplayOptions =
      { baseCss: Css.inputCard
      , additionalCss: Css.withNestedLabel
      , id_: "walletNickname"
      , placeholder: "Nickname"
      , readOnly: true
      , valueOptions: mempty
      }

    walletIdInputDisplayOptions =
      { baseCss: Css.inputCard
      , additionalCss: Css.withNestedLabel
      , id_: "walletId"
      , placeholder: "Wallet ID"
      , readOnly: true
      , valueOptions: mempty
      }
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ $ CloseCard PickupWalletCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
        [ p
            [ classNames [ "font-bold", "mb-4", "truncate", "w-11/12" ] ]
            [ text $ "Play wallet " <> view _value walletNicknameInput ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "walletNickname"
                  ]
                  [ text "Nickname" ]
              , WalletNicknameInputAction <$> renderInput walletNicknameInput walletNicknameInputDisplayOptions
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "walletId"
                ]
                [ text "Wallet ID" ]
            , WalletIdInputAction <$> renderInput walletIdInput walletIdInputDisplayOptions
            ]
        , div
            [ classNames [ "flex" ] ]
            [ button
                [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
                , onClick_ $ CloseCard PickupWalletCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , onClick_ $ PickupWallet $ view _value walletNicknameInput
                , disabled $ pickingUp || not isSuccess remoteWalletDetails
                ]
                [ text if pickingUp then "Picking up... " else "Pickup" ]
            ]
        ]
    ]

localWalletMissingCard :: forall p. Array (HTML p Action)
localWalletMissingCard =
  [ a
      [ classNames [ "absolute", "top-4", "right-4" ]
      , onClick_ $ CloseCard LocalWalletMissingCard
      ]
      [ icon_ Close ]
  , div [ classNames [ "flex", "font-semibold", "px-5", "py-4", "bg-gray" ] ]
      [ icon ErrorOutline [ "mr-2" ]
      , span_ [ text "Wallet not found" ]
      ]
  , div
      [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ p
          [ classNames [ "mb-4" ] ]
          [ text "A wallet that you have previously used is no longer available in our demo server. This is probably because the demo server has been updated. (Note that this demo is in continuous development, and data is not preserved between updates.) We recommend that you use the button below to clear your browser's cache for this site and start again." ]
      , div
          [ classNames [ "flex", "justify-center" ] ]
          [ button
              [ classNames Css.primaryButton
              , onClick_ ClearLocalStorage
              ]
              [ text "Clear Cache" ]
          ]
      ]
  ]

------------------------------------------------------------
renderPickupScreen :: forall p. Warn (Text "We need to add the documentation link.") => State -> HTML p Action
renderPickupScreen state =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "flex", "flex-col", "justify-between" ] ]
    [ header
        [ classNames [ "p-2" ] ]
        [ a
            [ classNames [ "flex", "p-2", "font-bold" ]
            , href "https://marlowe-finance.io"
            ]
            [ img
                [ classNames [ "mr-2" ]
                , src arrowBack
                ]
            , text "marlowe-finance.io"
            ]
        , div
            [ classNames [ "hidden", "md:block", "absolute", "top-20", "right-0", "p-8", "pt-6", "bg-white", "text-gray", "text-4xl", "font-semibold", "leading-none", "rounded-l-lg", "shadow-lg" ] ]
            [ text "ES" ]
        ]
    , pickupWalletScreen state
    , footer
        -- we give the footer a fixed height and the div inside it absolute positioning, because otherwise
        -- the div makes the `pickupWalletScreen` element above it too small
        [ classNames [ "h-22", "flex", "justify-between" ] ]
        [ div
            [ classNames [ "absolute", "bottom-0", "left-0", "bg-white", "p-8", "rounded-tr-lg", "shadow-lg" ] ]
            [ icon ArrowRight [ "hidden", "md:block", "text-medium-icon", "leading-none", "text-gray", "text-center", "mb-6" ]
            , a
                [ classNames [ "px-8", "py-4", "font-bold", "hover:bg-link-highlight", "bg-no-repeat", "bg-center" ]
                , href ""
                ]
                [ text "Docs" ]
            ]
        ]
    ]

pickupWalletScreen :: forall p. State -> HTML p Action
pickupWalletScreen state =
  let
    walletLibrary = view _walletLibrary state

    remoteWalletDetails = view _remoteWalletDetails state

    walletNicknameOrIdInput = view _walletNicknameOrIdInput state

    walletNicknameOrIdInputDisplayOptions =
      { baseCss: Css.inputNoFocus
      , additionalCss: [ "pr-9" ]
      , id_: "existingWallet"
      , placeholder: "Enter a wallet ID/nickname"
      , readOnly: false
      , valueOptions: List.toUnfoldable $ values $ view _walletNickname <$> walletLibrary
      }
  in
    main
      [ classNames [ "p-4", "max-w-sm", "mx-auto" ] ]
      [ img
          [ classNames [ "w-4/5", "mx-auto", "mb-6", "text-center" ]
          , src marloweRunLogo
          ]
      , p
          [ classNames [ "mb-4", "text-center" ] ]
          [ text "To use Marlowe Run, generate a new demo wallet." ]
      , button
          [ classNames $ Css.primaryButton <> [ "w-full", "mb-4", "text-center" ]
          , onClick_ GenerateWallet
          ]
          [ text "Generate demo wallet" ]
      , hr [ classNames [ "mb-4", "max-w-xs", "mx-auto" ] ]
      , p
          [ classNames [ "mb-4", "text-center" ] ]
          [ text "Or use an existing one by entering a wallet ID or nickname." ]
      , WalletNicknameOrIdInputAction <$> renderInput walletNicknameOrIdInput walletNicknameOrIdInputDisplayOptions
      ]
  where
  walletList walletDetails =
    a
      [ classNames [ "block", "p-4", "hover:bg-black", "hover:text-white" ]
      , onClick_ $ OpenPickupWalletCardWithDetails walletDetails
      ]
      [ text $ view _walletNickname walletDetails ]
