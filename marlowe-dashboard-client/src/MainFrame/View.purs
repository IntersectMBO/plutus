module MainFrame.View where

import Prelude hiding (div)
import Contract.View (contractsScreen, contractDetailsCard)
import Css (classNames, hideWhen)
import Data.Either (Either(..))
import Data.Lens (view)
import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (HTML, a, div, footer, h1, header, main, nav, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (href)
import MainFrame.Lenses (_card, _menuOpen, _newWalletNicknameKey, _screen, _subState, _wallet, _wallets)
import MainFrame.Types (Action(..), Card(..), ChildSlots, ContractStatus(..), WalletState, PickupCard(..), PickupScreen(..), PickupState, Screen(..), State)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Prim.TypeError (class Warn, Text)
import Template.View (templateLibraryCard, templateDetailsCard)
import Wallet.Types (WalletNicknameKey, WalletLibrary)
import Wallet.View (contactDetailsCard, newContactCard, pickupLocalWalletCard, pickupNewWalletCard, pickupWalletScreen, putdownWalletCard, walletLibraryScreen)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    wallets = view _wallets state

    newWalletNicknameKey = view _newWalletNicknameKey state
  in
    case view _subState state of
      Left pickupState -> renderPickupState wallets newWalletNicknameKey pickupState
      Right walletState -> renderWalletState wallets newWalletNicknameKey walletState

------------------------------------------------------------
renderPickupState :: forall p. WalletLibrary -> WalletNicknameKey -> PickupState -> HTML p Action
renderPickupState wallets newWalletNicknameKey pickupState =
  let
    screen = view _screen pickupState

    card = view _card pickupState
  in
    div
      [ classNames [ "grid", "h-full" ] ]
      [ main
          [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
          [ renderPickupCard card newWalletNicknameKey wallets
          , renderPickupScreen wallets screen
          ]
      ]

renderPickupCard :: forall p. Maybe PickupCard -> WalletNicknameKey -> WalletLibrary -> HTML p Action
renderPickupCard pickupCard newWalletNicknameKey wallets =
  div
    [ classNames $ [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen (isNothing pickupCard) ]
    [ div
        [ classNames $ [ "shadow-md", "bg-white", "mx-1", "md:mx-auto", "md:w-card" ] <> hideWhen (isNothing pickupCard) ]
        [ div
            [ classNames [ "flex", "justify-end" ] ]
            [ a
                [ classNames [ "p-0.5", "text-green" ]
                , onClick $ const $ Just $ SetPickupCard Nothing
                ]
                [ Icon.close ]
            ]
        , div
            [ classNames [ "px-1", "pb-1" ] ] case pickupCard of
            Just PickupNewWalletCard -> [ pickupNewWalletCard newWalletNicknameKey wallets ]
            Just (PickupWalletCard walletNicknameKey) -> [ pickupLocalWalletCard walletNicknameKey ]
            Nothing -> []
        ]
    ]

renderPickupScreen :: forall p. WalletLibrary -> PickupScreen -> HTML p Action
renderPickupScreen wallets screen = case screen of
  GenerateWalletScreen ->
    div
      [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0" ] ]
      [ pickupWalletScreen wallets ]

------------------------------------------------------------
renderWalletState :: forall p. WalletLibrary -> WalletNicknameKey -> WalletState -> HTML p Action
renderWalletState wallets newWalletNicknameKey walletState =
  let
    wallet = view _wallet walletState

    menuOpen = view _menuOpen walletState

    screen = view _screen walletState

    card = view _card walletState
  in
    div
      [ classNames [ "grid", "h-full", "grid-rows-main" ] ]
      [ renderHeader wallet wallets menuOpen
      , renderMain newWalletNicknameKey wallet wallets menuOpen screen card
      , renderFooter
      ]

renderHeader :: forall p. PubKey -> WalletLibrary -> Boolean -> HTML p Action
renderHeader wallet wallets menuOpen =
  header
    [ classNames [ "relative", "flex", "justify-between", "text-green" ] ]
    [ h1
        [ classNames $ itemClasses <> [ "cursor-pointer" ]
        , onClick $ const $ Just $ SetScreen $ ContractsScreen Running
        ]
        [ Icon.image
        , span
            [ classNames [ "ml-0.5" ] ]
            [ text "Demo" ]
        ]
    , nav
        [ classNames [ "flex" ] ]
        [ a
            [ classNames $ itemClasses <> [ "hidden", "md:flex" ]
            , onClick $ const $ Just $ SetScreen WalletLibraryScreen
            ]
            [ Icon.contacts
            , span
                [ classNames [ "ml-0.5" ] ]
                [ text "Contacts" ]
            ]
        , a
            [ classNames itemClasses
            , onClick $ const $ Just $ ToggleCard PutdownWalletCard
            ]
            [ Icon.wallet
            , span
                [ classNames [ "ml-0.5", "hidden", "md:inline" ] ]
                [ text "Wallet" ]
            ]
        , a
            [ classNames $ itemClasses <> [ "md:hidden" ]
            , onClick $ const $ Just ToggleMenu
            ]
            [ if menuOpen then Icon.close else Icon.menu ]
        , a
            [ classNames $ itemClasses <> [ "px-1", "bg-green", "text-white" ]
            , onClick $ const $ Just $ ToggleCard TemplateLibraryCard
            ]
            [ span
                [ classNames [ "mr-0.5" ] ]
                [ text "New" ]
            , Icon.libraryAdd
            ]
        ]
    ]
  where
  itemClasses = [ "flex", "items-center", "p-0.5" ]

renderMain :: forall p. WalletNicknameKey -> PubKey -> WalletLibrary -> Boolean -> Screen -> Maybe Card -> HTML p Action
renderMain newWalletNicknameKey wallet wallets menuOpen screen card =
  main
    [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
    [ renderMobileMenu menuOpen
    , renderCards newWalletNicknameKey wallets wallet card
    , renderScreen wallets screen
    ]

renderMobileMenu :: forall p. Boolean -> HTML p Action
renderMobileMenu menuOpen =
  div
    [ classNames $ [ "md:hidden", "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-20", "bg-transgray" ] <> hideWhen (not menuOpen) ]
    [ nav
        [ classNames $ [ "absolute", "top-0", "bottom-0.5", "left-0.5", "right-0.5", "bg-gray", "overflow-auto", "flex", "flex-col", "justify-between" ] ]
        [ div
            [ classNames [ "flex", "flex-col" ] ]
            $ [ link "Dashboard home" $ Right $ SetScreen $ ContractsScreen Running
              , link "Contacts" $ Right $ SetScreen WalletLibraryScreen
              ]
            <> dashboardLinks
        , div
            [ classNames [ "flex", "flex-col" ] ]
            iohkLinks
        ]
    ]

renderCards :: forall p. WalletNicknameKey -> WalletLibrary -> PubKey -> Maybe Card -> HTML p Action
renderCards newWalletNicknameKey wallets wallet card =
  div
    [ classNames $ [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen (isNothing card) ]
    [ div
        [ classNames $ [ "shadow-md", "bg-white", "mx-1", "md:mx-auto", "md:w-card" ] <> hideWhen (isNothing card) ]
        [ div
            [ classNames [ "flex", "justify-end" ] ]
            [ a
                [ classNames [ "p-0.5", "leading-none", "text-green" ]
                , onClick $ const $ Just $ SetCard Nothing
                ]
                [ Icon.close ]
            ]
        , div
            [ classNames [ "px-1", "pb-1" ] ] case card of
            Just CreateWalletCard -> [ newContactCard newWalletNicknameKey wallets ]
            Just (ViewWalletCard walletNicknameKey walletDetails) -> [ contactDetailsCard walletNicknameKey walletDetails ]
            Just PutdownWalletCard -> [ putdownWalletCard wallet wallets ]
            Just TemplateLibraryCard -> [ templateLibraryCard ]
            Just (ContractTemplateCard contractTemplate) -> [ templateDetailsCard contractTemplate ]
            Just (ContractInstanceCard contractInstance) -> [ ContractAction <$> contractDetailsCard contractInstance ]
            Nothing -> []
        ]
    ]

renderScreen :: forall p. WalletLibrary -> Screen -> HTML p Action
renderScreen wallets screen =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0" ] ]
    [ case screen of
        ContractsScreen contractStatus -> ContractAction <$> contractsScreen contractStatus
        WalletLibraryScreen -> walletLibraryScreen wallets
    ]

renderFooter :: forall p. HTML p Action
renderFooter =
  footer
    [ classNames [ "hidden", "md:flex", "justify-between" ] ]
    [ nav
        [ classNames [ "flex" ] ]
        dashboardLinks
    , nav
        [ classNames [ "flex" ] ]
        iohkLinks
    ]

dashboardLinks :: forall p. Warn (Text "We need to add the dashboard links.") => Array (HTML p Action)
dashboardLinks =
  [ link "Library" $ Left ""
  , link "Docs" $ Left ""
  , link "Support" $ Left ""
  ]

iohkLinks :: forall p. Warn (Text "We need to add the IOHK links.") => Array (HTML p Action)
iohkLinks =
  [ link "marlowe.io" $ Left ""
  , link "cardano.org" $ Left "https://cardano.org"
  , link "iohk.io" $ Left "https://iohk.io"
  ]

link :: forall p. String -> Either String Action -> HTML p Action
link label urlOrAction =
  a
    [ classNames [ "p-1", "text-green", "hover:underline", "cursor-pointer" ]
    , case urlOrAction of
        Left url -> href url
        Right action -> onClick $ const $ Just action
    ]
    [ text label ]
