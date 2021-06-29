module Welcome.View (renderWelcomeState) where

import Prelude hiding (div)
import Css (bgBlueGradient, classNames)
import Css as Css
import Data.Lens (view)
import Data.List (foldMap)
import Data.List (toUnfoldable) as List
import Data.Map (values)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, iframe, img, label, main, p, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (disabled, for, href, src, title)
import Images (backgroundShape, marloweRunLogo)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.Types (InputDisplayOptions)
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
        [ classNames $ [ "hidden", "lg:block", "absolute", "top-0", "right-0" ] ]
        [ img [ src backgroundShape ] ]
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
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "p-4", "z-0", "grid", "gap-8", "grid-rows-welcome", "lg:grid-cols-welcome" ] ]
    [ useWalletBox state
    , gettingStartedBox
    ]

useWalletBox :: forall p. State -> HTML p Action
useWalletBox state =
  let
    walletLibrary = view _walletLibrary state

    remoteWalletDetails = view _remoteWalletDetails state

    walletNicknameOrIdInput = view _walletNicknameOrIdInput state

    walletNicknameOrIdInputDisplayOptions =
      { baseCss: Css.inputNoFocus
      , additionalCss: mempty
      , id_: "existingWallet"
      , placeholder: "Choose wallet or paste key"
      , readOnly: false
      , valueOptions: List.toUnfoldable $ values $ view _walletNickname <$> walletLibrary
      }
  in
    main
      [ classNames [ "row-start-2", "lg:col-start-2", "bg-white", "rounded-lg", "shadow-lg", "p-8", "pt-12", "lg:px-12", "max-w-sm", "mx-auto", "lg:max-w-none", "lg:w-welcome-box" ] ]
      [ img
          [ classNames [ "mx-auto", "mb-6", "text-center" ]
          , src marloweRunLogo
          ]
      , p
          [ classNames [ "mb-4", "text-center" ] ]
          [ text "To being using the Marlowe Run demo, generate a new demo wallet." ]
      , button
          [ classNames $ Css.primaryButton <> [ "w-full", "mb-4", "text-center" ]
          , onClick_ GenerateWallet
          ]
          [ text "Generate demo wallet" ]
      , a
          [ classNames [ "block", "text-purple", "text-center", "font-semibold", "mb-4" ]
          , onClick_ $ OpenCard GenerateWalletHelpCard
          ]
          [ text "Why do I need to do this?" ]
      , hr [ classNames [ "mb-4", "max-w-xs", "mx-auto" ] ]
      , p
          [ classNames [ "mb-4", "text-center" ] ]
          [ text "Or select an existing demo wallet from the list or paste in a demo wallet key." ]
      , WalletNicknameOrIdInputAction <$> renderInput walletNicknameOrIdInput walletNicknameOrIdInputDisplayOptions
      , div
          [ classNames [ "mt-6", "flex", "justify-between" ] ]
          [ a
              [ classNames [ "flex", "font-bold" ]
              , href "https://staging.marlowe-web.iohkdev.io"
              ]
              [ icon_ Previous
              , text "Back to home page"
              ]
          , a
              [ classNames [ "font-bold" ]
              -- FIXME: add link to documentation
              , href ""
              ]
              [ text "Docs" ]
          ]
      ]
  where
  walletList walletDetails =
    a
      [ classNames [ "block", "p-4", "hover:bg-black", "hover:text-white" ]
      , onClick_ $ OpenConnectWalletCardWithDetails walletDetails
      ]
      [ text $ view _walletNickname walletDetails ]

gettingStartedBox :: forall p. HTML p Action
gettingStartedBox =
  div
    [ classNames [ "row-start-3", "lg:row-start-2", "lg:col-start-3", "max-w-sm", "mx-auto", "lg:max-w-none", "lg:w-welcome-box", "flex", "flex-col", "justify-center" ] ]
    [ a
        [ classNames [ "text-purple", "text-center", "lg:hidden" ]
        , onClick_ $ OpenCard GetStartedHelpCard
        ]
        [ icon Play $ bgBlueGradient <> [ "text-3xl", "text-white", "rounded-full" ]
        , br_
        , text "Watch our get started tutorial"
        ]
    , div
        [ classNames [ "hidden", "lg:block" ] ]
        [ a
            [ classNames [ "block", "relative", "rounded-lg", "shadow-lg", "bg-get-started-thumbnail", "bg-cover", "w-full", "h-welcome-box", "mb-6" ]
            , onClick_ $ OpenCard GetStartedHelpCard
            ]
            [ icon Play $ bgBlueGradient <> [ "absolute", "bottom-4", "right-4", "text-3xl", "text-white", "rounded-full" ] ]
        , p
            [ classNames [ "font-semibold", "text-lg", "text-center" ] ]
            [ text "New to Marlowe Run?" ]
        , p
            [ classNames [ "text-lg", "text-center" ] ]
            [ text "Watch our get started tutorial" ]
        ]
    ]

------------------------------------------------------------
renderWelcomeCard :: forall p. State -> HTML p Action
renderWelcomeCard state =
  let
    card = view _card state

    cardClasses = if card == Just GetStartedHelpCard then Css.videoCard else Css.card
  in
    div
      [ classNames $ Css.overlay $ isNothing card ]
      [ div
          [ classNames $ cardClasses $ isNothing card ]
          $ (flip foldMap card) \cardType -> case cardType of
              GetStartedHelpCard -> getStartedHelpCard
              GenerateWalletHelpCard -> generateWalletHelpCard
              ConnectNewWalletCard -> connectNewWalletCard state
              ConnectWalletCard -> connectWalletCard state
              LocalWalletMissingCard -> localWalletMissingCard
      ]

getStartedHelpCard :: forall p. Array (HTML p Action)
getStartedHelpCard =
  [ a
      [ classNames [ "absolute", "-top-10", "right-0", "lg:-right-10" ]
      , onClick_ $ CloseCard GetStartedHelpCard
      ]
      [ icon Close [ "text-lg", "rounded-full", "bg-white", "p-2" ] ]
  , div
      [ classNames $ Css.embeddedVideoContainer <> [ "rounded", "overflow-hidden" ] ]
      [ iframe
          [ classNames Css.embeddedVideo
          -- FIXME: add link to the right video (when it's ready)
          , src "https://www.youtube.com/embed/WB-bYHleFYY"
          , title "Get started video"
          ]
      ]
  ]

generateWalletHelpCard :: forall p. Array (HTML p Action)
generateWalletHelpCard =
  [ div
      [ classNames Css.embeddedVideoContainer ]
      [ iframe
          [ classNames Css.embeddedVideo
          -- FIXME: add link to the right video (when it's ready)
          , src "https://www.youtube.com/embed/WB-bYHleFYY"
          , title "YouTube video player"
          ]
      ]
  , div
      [ classNames [ "p-5", "pb-6", "lg:pb-8" ] ]
      [ h2
          [ classNames [ "font-semibold", "mb-4" ] ]
          [ text "Why generate a demo wallet?" ]
      , p
          [ classNames [ "mb-4" ] ]
          [ text "Demo wallets are used so you can play around with the app and all its incredible features without using your own tokens from your real wallet." ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1", "mr-4" ]
              , onClick_ $ CloseCard GenerateWalletHelpCard
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ $ CloseCard GenerateWalletHelpCard
              ]
              [ text "Got it" ]
          ]
      ]
  ]

connectNewWalletCard :: forall p. State -> Array (HTML p Action)
connectNewWalletCard state =
  let
    connecting = view _connecting state

    remoteWalletDetails = view _remoteWalletDetails state

    walletNicknameInput = view _walletNicknameInput state

    walletIdInput = view _walletIdInput state
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ $ CloseCard ConnectNewWalletCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "lg:pb-8" ] ]
        [ h2
            [ classNames [ "font-bold", "my-4" ] ]
            [ text $ "Demo wallet generated" ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "walletNickname"
                  ]
                  [ text "Nickname" ]
              , WalletNicknameInputAction <$> renderInput walletNicknameInput (walletNicknameInputDisplayOptions false)
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "walletID"
                ]
                [ text "Wallet ID" ]
            , WalletIdInputAction <$> renderInput walletIdInput walletIdInputDisplayOptions
            , walletIdTip
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
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ $ CloseCard ConnectWalletCard
        ]
        [ icon_ Close ]
    , div [ classNames [ "p-5", "pb-6", "lg:pb-8" ] ]
        [ h2
            [ classNames [ "font-bold", "my-4", "truncate", "w-11/12" ] ]
            [ text $ "Demo wallet " <> view _value walletNicknameInput ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "walletNickname"
                  ]
                  [ text "Nickname" ]
              , WalletNicknameInputAction <$> renderInput walletNicknameInput (walletNicknameInputDisplayOptions true)
              ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            [ label
                [ classNames Css.nestedLabel
                , for "walletId"
                ]
                [ text "Wallet ID" ]
            , WalletIdInputAction <$> renderInput walletIdInput walletIdInputDisplayOptions
            , walletIdTip
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

walletNicknameInputDisplayOptions :: Boolean -> InputDisplayOptions
walletNicknameInputDisplayOptions readOnly =
  { baseCss: Css.inputCard
  , additionalCss: Css.withNestedLabel
  , id_: "walletNickname"
  , placeholder: if readOnly then mempty else "Give your wallet a nickname"
  , readOnly
  , valueOptions: mempty
  }

walletIdInputDisplayOptions :: InputDisplayOptions
walletIdInputDisplayOptions =
  { baseCss: Css.inputCard
  , additionalCss: Css.withNestedLabel
  , id_: "walletId"
  , placeholder: "Wallet ID"
  , readOnly: true
  , valueOptions: mempty
  }

walletIdTip :: forall p. HTML p Action
walletIdTip =
  p
    [ classNames [ "text-sm", "font-semibold" ] ]
    [ text "Tip: Copy and share your wallet ID with others so they can add you to their contracts" ]

localWalletMissingCard :: forall p. Array (HTML p Action)
localWalletMissingCard =
  [ div
      [ classNames $ Css.card false ]
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
          [ classNames [ "p-5", "pb-6", "lg:pb-8" ] ]
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
  ]
