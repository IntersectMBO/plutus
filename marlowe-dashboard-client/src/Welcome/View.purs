module Welcome.View
  ( welcomeScreen
  , welcomeCard
  ) where

import Prelude hiding (div)
import Clipboard (Action(..)) as Clipboard
import Css as Css
import Data.Lens (view, (^.))
import Data.List (foldMap)
import Data.List (toUnfoldable) as List
import Data.Map (values)
import Data.Maybe (Maybe(..), isJust)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, a, br_, button, div, h2, hr, iframe, img, label, main, p, section, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (disabled, for, href, src, title)
import Images (marloweRunLogo)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.Types (InputDisplayOptions)
import InputField.View (renderInput)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Network.RemoteData (isSuccess)
import Prim.TypeError (class Warn, Text)
import WalletData.Lenses (_walletNickname)
import WalletData.View (walletIdTip)
import Welcome.Lenses (_card, _cardOpen, _enteringDashboardState, _remoteWalletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Card(..), State)

welcomeScreen :: forall p. State -> HTML p Action
welcomeScreen state =
  main
    [ classNames
        [ "h-full"
        , "overflow-x-hidden"
        , "grid"
        , "gap-8"
        , "grid-rows-1fr-auto-auto-1fr"
        , "lg:grid-rows-1fr-auto-1fr"
        , "lg:grid-cols-1fr-auto-auto-1fr"
        , "bg-background-shape"
        , "bg-right-top"
        , "bg-no-repeat"
        , "p-4"
        ]
    ]
    [ useWalletBox state
    , gettingStartedBox
    ]

welcomeCard :: forall p. State -> HTML p Action
welcomeCard state =
  let
    card = state ^. _card

    cardOpen = state ^. _cardOpen

    cardClasses = if card == Just GetStartedHelpCard then Css.videoCard else Css.card
  in
    div
      [ classNames $ Css.cardOverlay cardOpen ]
      [ div
          [ classNames $ cardClasses cardOpen ]
          $ (flip foldMap card) \cardType -> case cardType of
              GetStartedHelpCard -> getStartedHelpCard
              GenerateWalletHelpCard -> generateWalletHelpCard
              UseNewWalletCard -> useNewWalletCard state
              UseWalletCard -> useWalletCard state
              LocalWalletMissingCard -> localWalletMissingCard
      ]

------------------------------------------------------------
useWalletBox :: forall p. Warn (Text "We need to add the documentation link.") => State -> HTML p Action
useWalletBox state =
  let
    walletLibrary = state ^. _walletLibrary

    remoteWalletDetails = state ^. _remoteWalletDetails

    walletNicknameOrIdInput = state ^. _walletNicknameOrIdInput

    walletNicknameOrIdInputDisplayOptions =
      { additionalCss: mempty
      , id_: "existingWallet"
      , placeholder: "Choose wallet or paste key"
      , readOnly: false
      , numberFormat: Nothing
      , valueOptions: List.toUnfoldable $ values $ view _walletNickname <$> walletLibrary
      }
  in
    section
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
      , WalletNicknameOrIdInputAction <$> renderInput walletNicknameOrIdInputDisplayOptions walletNicknameOrIdInput
      , div
          [ classNames [ "mt-6", "flex", "justify-between" ] ]
          [ a
              [ classNames [ "flex", "font-bold" ]
              , href "https://staging.marlowe-web.iohkdev.io"
              ]
              [ icon_ Icon.Previous
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
      , onClick_ $ OpenUseWalletCardWithDetails walletDetails
      ]
      [ text $ walletDetails ^. _walletNickname ]

gettingStartedBox :: forall p. HTML p Action
gettingStartedBox =
  section
    [ classNames [ "row-start-3", "lg:row-start-2", "lg:col-start-3", "max-w-sm", "mx-auto", "lg:max-w-none", "lg:w-welcome-box", "flex", "flex-col", "justify-center" ] ]
    [ a
        [ classNames [ "text-purple", "text-center", "lg:hidden" ]
        , onClick_ $ OpenCard GetStartedHelpCard
        ]
        [ icon Icon.Play $ Css.bgBlueGradient <> [ "text-3xl", "text-white", "rounded-full" ]
        , br_
        , text "Watch our get started tutorial"
        ]
    , div
        [ classNames [ "hidden", "lg:block" ] ]
        [ a
            [ classNames [ "block", "relative", "rounded-lg", "shadow-lg", "bg-get-started-thumbnail", "bg-cover", "w-full", "h-welcome-box", "mb-6" ]
            , onClick_ $ OpenCard GetStartedHelpCard
            ]
            [ icon Icon.Play $ Css.bgBlueGradient <> [ "absolute", "bottom-4", "right-4", "text-3xl", "text-white", "rounded-full" ] ]
        , p
            [ classNames [ "font-semibold", "text-lg", "text-center" ] ]
            [ text "New to Marlowe Run?" ]
        , p
            [ classNames [ "text-lg", "text-center" ] ]
            [ text "Watch our get started tutorial" ]
        ]
    ]

------------------------------------------------------------
getStartedHelpCard :: forall p. Array (HTML p Action)
getStartedHelpCard =
  [ a
      [ classNames [ "absolute", "-top-10", "right-0", "lg:-right-10" ]
      , onClick_ CloseCard
      ]
      [ icon Icon.Close [ "text-lg", "rounded-full", "bg-white", "p-2" ] ]
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
          [ classNames [ "flex", "gap-4" ] ]
          [ button
              [ classNames $ Css.secondaryButton <> [ "flex-1" ]
              , onClick_ CloseCard
              ]
              [ text "Cancel" ]
          , button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ CloseCard
              ]
              [ text "Got it" ]
          ]
      ]
  ]

useNewWalletCard :: forall p. State -> Array (HTML p Action)
useNewWalletCard state =
  let
    enteringDashboardState = state ^. _enteringDashboardState

    remoteWalletDetails = state ^. _remoteWalletDetails

    walletNicknameInput = state ^. _walletNicknameInput

    walletNickname = walletNicknameInput ^. _value

    walletIdInput = state ^. _walletIdInput

    walletId = walletIdInput ^. _value
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ CloseCard
        ]
        [ icon_ Icon.Close ]
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
                  [ text "Wallet nickname" ]
              , WalletNicknameInputAction <$> renderInput (walletNicknameInputDisplayOptions false) walletNicknameInput
              ]
        , div
            [ classNames [ "relative", "mb-4" ] ]
            [ div
                [ classNames Css.hasNestedLabel ]
                [ label
                    [ classNames Css.nestedLabel
                    , for "walletID"
                    ]
                    [ text "Demo wallet ID" ]
                , WalletIdInputAction <$> renderInput walletIdInputDisplayOptions walletIdInput
                ]
            , walletIdTip
            , a
                [ classNames [ "w-6", "absolute", "top-10", "right-4" ]
                , onClick_ $ ClipboardAction $ Clipboard.CopyToClipboard walletId
                ]
                [ icon Icon.Copy [ "w-6" ] ]
            ]
        , div
            [ classNames [ "flex", "gap-4" ] ]
            [ button
                [ classNames $ Css.secondaryButton <> [ "flex-1" ]
                , onClick_ CloseCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , disabled $ isJust (validate walletNicknameInput) || enteringDashboardState || not isSuccess remoteWalletDetails
                , onClick_ $ UseWallet walletNickname
                ]
                [ text if enteringDashboardState then "Loading..." else "Use" ]
            ]
        ]
    ]

useWalletCard :: forall p. State -> Array (HTML p Action)
useWalletCard state =
  let
    enteringDashboardState = state ^. _enteringDashboardState

    remoteWalletDetails = state ^. _remoteWalletDetails

    walletNicknameInput = state ^. _walletNicknameInput

    walletNickname = walletNicknameInput ^. _value

    walletIdInput = state ^. _walletIdInput

    walletId = walletIdInput ^. _value
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ CloseCard
        ]
        [ icon_ Icon.Close ]
    , div [ classNames [ "p-5", "pb-6", "lg:pb-8" ] ]
        [ h2
            [ classNames [ "font-bold", "my-4", "truncate", "w-11/12" ] ]
            [ text $ "Demo wallet " <> walletNickname ]
        , div
            [ classNames $ Css.hasNestedLabel <> [ "mb-4" ] ]
            $ [ label
                  [ classNames $ Css.nestedLabel
                  , for "walletNickname"
                  ]
                  [ text "Wallet nickname" ]
              , WalletNicknameInputAction <$> renderInput (walletNicknameInputDisplayOptions true) walletNicknameInput
              ]
        , div
            [ classNames [ "relative", "mb-4" ] ]
            [ div
                [ classNames Css.hasNestedLabel ]
                [ label
                    [ classNames Css.nestedLabel
                    , for "walletID"
                    ]
                    [ text "Demo wallet ID" ]
                , WalletIdInputAction <$> renderInput walletIdInputDisplayOptions walletIdInput
                ]
            , walletIdTip
            , a
                [ classNames [ "w-6", "absolute", "top-10", "right-4" ]
                , onClick_ $ ClipboardAction $ Clipboard.CopyToClipboard walletId
                ]
                [ icon Icon.Copy [ "w-6" ] ]
            ]
        , div
            [ classNames [ "flex", "gap-4" ] ]
            [ button
                [ classNames $ Css.secondaryButton <> [ "flex-1" ]
                , onClick_ CloseCard
                ]
                [ text "Cancel" ]
            , button
                [ classNames $ Css.primaryButton <> [ "flex-1" ]
                , onClick_ $ UseWallet walletNickname
                , disabled $ enteringDashboardState || not isSuccess remoteWalletDetails
                ]
                [ text if enteringDashboardState then "Loading..." else "Use" ]
            ]
        ]
    ]

walletNicknameInputDisplayOptions :: Boolean -> InputDisplayOptions
walletNicknameInputDisplayOptions readOnly =
  { additionalCss: mempty
  , id_: "walletNickname"
  , placeholder: if readOnly then mempty else "Give your wallet a nickname"
  , readOnly
  , numberFormat: Nothing
  , valueOptions: mempty
  }

walletIdInputDisplayOptions :: InputDisplayOptions
walletIdInputDisplayOptions =
  { additionalCss: [ "font-mono", "text-xs", "pt-5" ]
  , id_: "walletId"
  , placeholder: "Demo wallet ID"
  , readOnly: true
  , numberFormat: Nothing
  , valueOptions: mempty
  }

localWalletMissingCard :: forall p. Array (HTML p Action)
localWalletMissingCard =
  [ div
      [ classNames $ Css.card true ]
      [ a
          [ classNames [ "absolute", "top-4", "right-4" ]
          , onClick_ CloseCard
          ]
          [ icon_ Icon.Close ]
      , div [ classNames [ "flex", "font-semibold", "px-5", "py-4", "bg-gray" ] ]
          [ icon Icon.ErrorOutline [ "mr-2" ]
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
