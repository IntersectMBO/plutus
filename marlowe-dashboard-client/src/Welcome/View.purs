module Welcome.View (renderWelcomeState) where

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
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_walletNickname)
import Welcome.Lenses (_card, _connecting, _remoteWalletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Card(..), State)

renderWelcomeState :: forall p. State -> HTML p Action
renderWelcomeState state =
  div
    [ classNames [ "grid", "h-full", "relative", "overflow-x-hidden" ] ]
    [ div
        [ classNames
            $ [ "absolute", "top-0", "-right-64", "w-160", "h-32", "bg-link-highlight", "bg-cover", "opacity-10", "transform", "rotate-180" ]
            <> [ "md:w-256", "md:h-48" ]
        ]
        []
    , main
        [ classNames [ "relative" ] ]
        -- In the Play view, there are potentially many cards all inside a containing div,
        -- and the last one has a semi-transparent overlay (using class "last:bg-overlay").
        -- Here in the Welcome view there is at most one card, but we need to put it inside
        -- a containing div as well, so that it's the last child, and has the bg-overlay
        -- applied.
        [ div_ [ renderWelcomeCard state ]
        , renderWelcomeScreen state
        ]
    ]

------------------------------------------------------------
renderWelcomeScreen :: forall p. Warn (Text "We need to add the documentation link.") => State -> HTML p Action
renderWelcomeScreen state =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "grid", "gap-4", "grid-rows-welcome", "md:grid-cols-welcome" ] ]
    [ useWallet state
    , gettingStarted
    ]

useWallet :: forall p. State -> HTML p Action
useWallet state =
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
      [ classNames [ "row-start-2", "md:col-start-2", "bg-white", "rounded-lg", "shadow-lg", "p-4", "max-w-sm", "mx-auto" ] ]
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
      , onClick_ $ OpenConnectWalletCardWithDetails walletDetails
      ]
      [ text $ view _walletNickname walletDetails ]

gettingStarted :: forall p. HTML p Action
gettingStarted =
  div
    [ classNames [ "row-start-3", "md:row-start-2", "md:col-start-3", "max-w-sm", "mx-auto", "flex", "flex-col", "justify-center" ] ]
    [ a
        [ classNames [ "text-purple" ] ]
        [ text "Watch our get started tutorial"]
    ]

------------------------------------------------------------
renderWelcomeCard :: forall p. State -> HTML p Action
renderWelcomeCard state =
  let
    card = view _card state
  in
    div
      [ classNames $ Css.overlay $ isNothing card ]
      [ div
          [ classNames $ Css.card $ isNothing card ]
          $ (flip foldMap card) \cardType -> case cardType of
              ConnectNewWalletCard -> connectNewWalletCard state
              ConnectWalletCard -> connectWalletCard state
              LocalWalletMissingCard -> localWalletMissingCard
      ]

connectNewWalletCard :: forall p. State -> Array (HTML p Action)
connectNewWalletCard state =
  let
    connecting = view _connecting state

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
        , onClick_ $ CloseCard ConnectNewWalletCard
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
                , onClick_ $ CloseCard ConnectNewWalletCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , disabled $ isJust (validate walletNicknameInput) || connecting || not isSuccess remoteWalletDetails
                , onClick_ $ ConnectWallet $ view _value walletNicknameInput
                ]
                [ text if connecting then "Connecting... " else "Use" ]
            ]
        ]
    ]

connectWalletCard :: forall p. State -> Array (HTML p Action)
connectWalletCard state =
  let
    connecting = view _connecting state

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
        , onClick_ $ CloseCard ConnectWalletCard
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
                , onClick_ $ CloseCard ConnectWalletCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , onClick_ $ ConnectWallet $ view _value walletNicknameInput
                , disabled $ connecting || not isSuccess remoteWalletDetails
                ]
                [ text if connecting then "Connecting... " else "Use" ]
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
