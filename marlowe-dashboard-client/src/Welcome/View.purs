module Welcome.View
  ( welcomeScreen
  , welcomeModal
  ) where

import Prologue hiding (div)
import Clipboard (Action(..)) as Clipboard
import Component.Input as Input
import Component.Label as Label
import Component.WalletId as WalletId
import Contacts.Lenses (_walletNickname)
import Contacts.Types (WalletNicknameError, WalletNickname)
import Contacts.View (walletIdTip)
import Css as Css
import Data.Filterable (filter)
import Data.Lens (set, view, (^.))
import Data.List (toUnfoldable) as List
import Data.Map (values)
import Data.Maybe (isNothing)
import Data.Newtype (unwrap)
import Data.Tuple.Nested ((/\))
import Data.UUID (toString) as UUID
import Halogen.Css (classNames)
import Halogen.HTML (HTML, a, br_, button, div, div_, h2, hr, iframe, img, main, p, p_, section, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (disabled, href, src, title)
import Images (marloweRunLogo)
import InputField.Lenses (_value)
import InputField.State (validate)
import InputField.Types as InputField
import InputField.View (renderInput)
import Marlowe.PAB (PlutusAppId)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Network.RemoteData (toMaybe)
import Prim.TypeError (class Warn, Text)
import Welcome.Lenses (_enteringDashboardState, _remoteWalletDetails, _walletLibrary, _walletNicknameOrIdInput)
import Welcome.Types (Action(..), Modal(..), State)

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

welcomeModal :: forall p. State -> HTML p Action
welcomeModal state@{ modal } = case modal of
  Just (GetStartedHelp /\ open) -> layout Css.videoCard open getStartedHelp
  Just (GenerateWalletHelp /\ open) -> layout Css.card open generateWalletHelp
  Just (UseNewWallet name id /\ open) -> layout Css.card open $ useNewWallet name id state
  Just (UseWallet name id /\ open) -> layout Css.card open $ useWallet name id state
  Just (LocalWalletMissing /\ open) -> layout Css.card open localWalletMissing
  _ -> layout Css.card false []
  where
  layout classes open contents =
    div [ classNames $ Css.cardOverlay open ]
      [ div [ classNames $ classes open ] contents
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
      , after: Nothing
      , before: Nothing
      }
  in
    section
      [ classNames [ "row-start-2", "lg:col-start-2", "bg-white", "rounded-lg", "shadow-lg", "p-8", "lg:p-12", "max-w-sm", "mx-auto", "lg:max-w-none", "lg:w-welcome-box", "space-y-4" ] ]
      [ div [ classNames [ "p-2 pt-0" ] ]
          [ img
              [ classNames [ "mx-auto", "text-center" ]
              , src marloweRunLogo
              ]
          ]
      , p
          [ classNames [ "text-center" ] ]
          [ text "To begin using the Marlowe Run demo, generate a new demo wallet." ]
      , button
          [ classNames $ Css.primaryButton <> [ "w-full", "text-center" ]
          , onClick_ GenerateWallet
          ]
          [ text "Generate demo wallet" ]
      , a
          [ classNames [ "block", "text-purple", "text-center", "font-semibold" ]
          , onClick_ $ OpenModal GenerateWalletHelp
          ]
          [ text "Why do I need to do this?" ]
      , hr [ classNames [ "max-w-xs", "mx-auto" ] ]
      , p
          [ classNames [ "text-center" ] ]
          [ text "Or select an existing demo wallet from the list or paste in a demo wallet key." ]
      , WalletNicknameOrIdInputAction <$> renderInput walletNicknameOrIdInputDisplayOptions walletNicknameOrIdInput
      , div
          [ classNames [ "pt-2", "flex", "justify-between" ] ]
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
      , onClick_ $ OpenUseWalletModalWithDetails walletDetails
      ]
      [ text $ walletDetails ^. _walletNickname ]

gettingStartedBox :: forall p. HTML p Action
gettingStartedBox =
  section
    [ classNames [ "row-start-3", "lg:row-start-2", "lg:col-start-3", "max-w-sm", "mx-auto", "lg:max-w-none", "lg:w-welcome-box", "flex", "flex-col", "justify-center" ] ]
    [ a
        [ classNames [ "text-purple", "text-center", "lg:hidden" ]
        , onClick_ $ OpenModal GetStartedHelp
        ]
        [ icon Icon.Play $ Css.bgBlueGradient <> [ "text-3xl", "text-white", "rounded-full" ]
        , br_
        , text "Watch our get started tutorial"
        ]
    , div
        [ classNames [ "hidden", "lg:block", "space-y-6" ] ]
        [ a
            [ classNames [ "block", "relative", "rounded-lg", "shadow-lg", "bg-get-started-thumbnail", "bg-cover", "w-full", "h-welcome-box" ]
            , onClick_ $ OpenModal GetStartedHelp
            ]
            [ icon Icon.Play $ Css.bgBlueGradient <> [ "absolute", "bottom-4", "right-4", "text-3xl", "text-white", "rounded-full" ] ]
        , div_
            [ p
                [ classNames [ "font-semibold", "text-lg", "text-center" ] ]
                [ text "New to Marlowe Run?" ]
            , p
                [ classNames [ "text-lg", "text-center" ] ]
                [ text "Watch our get started tutorial" ]
            ]
        ]
    ]

------------------------------------------------------------
getStartedHelp :: forall p. Array (HTML p Action)
getStartedHelp =
  [ a
      [ classNames [ "absolute", "-top-10", "right-0", "lg:-right-10" ]
      , onClick_ CloseModal
      ]
      [ icon Icon.Close [ "text-lg", "rounded-full", "bg-white", "p-2" ] ]
  , div
      [ classNames $ Css.embeddedVideoContainer <> [ "rounded", "overflow-hidden" ] ]
      [ iframe
          [ classNames Css.embeddedVideo
          , src "https://www.youtube.com/embed/PJLtKJJMH0U"
          , title "Get started video"
          ]
      ]
  ]

generateWalletHelp :: forall p. Array (HTML p Action)
generateWalletHelp =
  [ div
      [ classNames [ "p-5", "pb-6", "lg:pb-8", "space-y-4" ] ]
      [ h2
          [ classNames [ "font-semibold" ] ]
          [ text "Why generate a demo wallet?" ]
      , p_
          [ text "Demo wallets are used so you can play around with the app and all its incredible features without using your own tokens from your real wallet." ]
      , div
          [ classNames [ "flex" ] ]
          [ button
              [ classNames $ Css.primaryButton <> [ "flex-1" ]
              , onClick_ CloseModal
              ]
              [ text "Got it" ]
          ]
      ]
  ]

useNewWallet ::
  forall p.
  InputField.State WalletNicknameError ->
  PlutusAppId ->
  State ->
  Array (HTML p Action)
useNewWallet walletNicknameInput =
  let
    walletNickname = walletNicknameInput ^. _value

    walletNicknameInputDisplayOptions =
      { additionalCss: mempty
      , id_: nicknameId
      , placeholder: "Give your wallet a nickname"
      , readOnly: false
      , numberFormat: Nothing
      , valueOptions: mempty
      , after: Nothing
      , before: Just nicknameLabel
      }
  in
    useWallet'
      "Demo wallet generated"
      (isNothing $ validate walletNicknameInput)
      ( WalletNicknameInputAction
          <$> renderInput walletNicknameInputDisplayOptions walletNicknameInput
      )
      walletNickname

useWallet :: forall p. WalletNickname -> PlutusAppId -> State -> Array (HTML p Action)
useWallet nickname =
  useWallet'
    ("Demo wallet " <> nickname)
    true
    ( Input.renderWithChildren
        Input.defaultInput { id = nicknameId, value = nickname }
        (\input -> [ input, nicknameLabel ])
    )
    nickname

useWallet' ::
  forall p.
  String ->
  Boolean ->
  HTML p Action ->
  WalletNickname ->
  PlutusAppId ->
  State ->
  Array (HTML p Action)
useWallet' title canConnect nicknameInput walletNickname walletId state =
  let
    enteringDashboardState = state ^. _enteringDashboardState

    remoteWalletDetails = state ^. _remoteWalletDetails

    copyWalletId = (ClipboardAction <<< Clipboard.CopyToClipboard <<< UUID.toString <<< unwrap)
  in
    [ a
        [ classNames [ "absolute", "top-4", "right-4" ]
        , onClick_ CloseModal
        ]
        [ icon_ Icon.Close ]
    , div [ classNames [ "p-5", "lg:p-6", "space-y-4" ] ]
        [ h2
            [ classNames [ "font-bold", "truncate", "w-11/12" ] ]
            [ text title ]
        , nicknameInput
        , div
            [ classNames [] ]
            [ copyWalletId <$> WalletId.render WalletId.defaultInput { label = "Demo wallet ID", value = walletId }
            , walletIdTip
            ]
        , div
            [ classNames [ "flex", "gap-4" ] ]
            [ button
                [ classNames $ Css.secondaryButton <> [ "flex-1" ]
                , onClick_ CloseModal
                ]
                [ text "Cancel" ]
            , button
                ( [ classNames $ Css.primaryButton <> [ "flex-1" ] ]
                    <> ( remoteWalletDetails
                          # toMaybe
                          # filter (const $ canConnect && not enteringDashboardState)
                          # map (set _walletNickname walletNickname)
                          # case _ of
                              Just walletDetails -> [ onClick_ $ ConnectWallet walletDetails ]
                              Nothing -> [ disabled true ]
                      )
                )
                [ text if enteringDashboardState then "Connecting..." else "Connect Wallet" ]
            ]
        ]
    ]

localWalletMissing :: forall p. Array (HTML p Action)
localWalletMissing =
  [ div
      [ classNames $ Css.card true ]
      [ a
          [ classNames [ "absolute", "top-4", "right-4" ]
          , onClick_ CloseModal
          ]
          [ icon_ Icon.Close ]
      , div [ classNames [ "flex", "font-semibold", "gap-2", "px-5", "py-4", "bg-gray" ] ]
          [ icon Icon.ErrorOutline []
          , span_ [ text "Wallet not found" ]
          ]
      , div
          [ classNames [ "p-5", "pb-6", "lg:pb-8", "space-y-4" ] ]
          [ p_
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

nicknameId :: String
nicknameId = "walletNickname"

nicknameLabel :: forall w i. HTML w i
nicknameLabel =
  Label.render
    Label.defaultInput { for = nicknameId, text = "Wallet nickname" }
