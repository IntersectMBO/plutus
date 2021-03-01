module Play.View (renderPlayState) where

import Prelude hiding (div)
import Contract.Types (State) as Contract
import Contract.View (contractsScreen, contractDetailsCard)
import Css (classNames, hideWhen)
import Data.Either (Either(..))
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isNothing)
import Halogen.HTML (HTML, a, div, footer, h1, header, main, nav, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href)
import MainFrame.Lenses (_card, _screen)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Play.Lenses (_contractState, _menuOpen, _templateState, _wallet)
import Play.Types (Action(..), Card(..), ContractStatus(..), Screen(..), State)
import Prim.TypeError (class Warn, Text)
import Template.Types (State) as Template
import Template.Types (Template)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import WalletData.Types (WalletLibrary, WalletNicknameKey)
import WalletData.View (newWalletCard, walletDetailsCard, putdownWalletCard, walletLibraryScreen)

renderPlayState :: forall p. WalletLibrary -> WalletNicknameKey -> Array Template -> State -> HTML p Action
renderPlayState wallets newWalletNicknameKey templates playState =
  let
    wallet = view _wallet playState

    menuOpen = view _menuOpen playState
  in
    div
      [ classNames [ "grid", "h-full", "grid-rows-main" ] ]
      [ renderHeader wallet menuOpen
      , renderMain newWalletNicknameKey wallets templates playState
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall p. PubKey -> Boolean -> HTML p Action
renderHeader wallet menuOpen =
  header
    [ classNames [ "relative", "flex", "justify-between", "text-green" ] ]
    [ h1
        [ classNames $ itemClasses <> [ "cursor-pointer" ]
        , onClick_ $ SetScreen $ ContractsScreen Running
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
            , onClick_ $ SetScreen WalletLibraryScreen
            ]
            [ Icon.contacts
            , span
                [ classNames [ "ml-0.5" ] ]
                [ text "Contacts" ]
            ]
        , a
            [ classNames itemClasses
            , onClick_ $ ToggleCard PutdownWalletCard
            ]
            [ Icon.wallet
            , span
                [ classNames [ "ml-0.5", "hidden", "md:inline" ] ]
                [ text "Wallet" ]
            ]
        , a
            [ classNames $ itemClasses <> [ "md:hidden" ]
            , onClick_ ToggleMenu
            ]
            [ if menuOpen then Icon.close else Icon.menu ]
        , a
            [ classNames $ itemClasses <> [ "px-1", "bg-green", "text-white" ]
            , onClick_ $ ToggleCard TemplateLibraryCard
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

------------------------------------------------------------
renderMain :: forall p. WalletNicknameKey -> WalletLibrary -> Array Template -> State -> HTML p Action
renderMain newWalletNicknameKey wallets templates playState =
  let
    wallet = view _wallet playState

    menuOpen = view _menuOpen playState

    screen = view _screen playState

    card = view _card playState

    templateState = view _templateState playState

    contractState = view _contractState playState
  in
    main
      [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
      [ renderMobileMenu menuOpen
      , renderCards newWalletNicknameKey wallets templates wallet card contractState
      , renderScreen wallets screen templateState
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

renderCards :: forall p. WalletNicknameKey -> WalletLibrary -> Array Template -> PubKey -> Maybe Card -> Contract.State -> HTML p Action
renderCards newWalletNicknameKey wallets templates wallet card contractState =
  div
    [ classNames $ [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "flex", "flex-col", "justify-end", "md:justify-center", "bg-transgray" ] <> hideWhen (isNothing card) ]
    [ div
        [ classNames cardClasses ]
        [ div
            [ classNames [ "flex", "justify-end" ] ]
            [ a
                [ classNames [ "p-0.5", "leading-none", "text-green" ]
                , onClick_ $ SetCard Nothing
                ]
                [ Icon.close ]
            ]
        , div
            [ classNames [ "px-1", "pb-1" ] ]
            $ (flip foldMap card) \cardType -> case cardType of
                CreateWalletCard -> [ newWalletCard newWalletNicknameKey wallets ]
                ViewWalletCard walletNicknameKey walletDetails -> [ walletDetailsCard walletNicknameKey walletDetails ]
                PutdownWalletCard -> [ putdownWalletCard wallet wallets ]
                TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard templates ]
                NewContractForRoleCard -> []
                ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard ]
                ContractCard -> [ ContractAction <$> contractDetailsCard contractState ]
        ]
    ]
  where
  cardClasses = case card of
    Just TemplateLibraryCard -> [ "max-h-full", "overflow-auto", "mt-3", "mx-1", "shadow-md", "bg-gray", "md:mb-3", "lg:mx-3" ]
    Just ContractCard -> [ "max-h-full", "overflow-auto", "mt-1", "mx-1", "shadow-md", "bg-gray", "md:mb-1", "lg:mx-3" ]
    Just _ -> [ "mx-1", "shadow-md", "bg-white", "md:mx-auto", "md:w-card" ]
    Nothing -> [ "hidden" ]

renderScreen :: forall p. WalletLibrary -> Screen -> Template.State -> HTML p Action
renderScreen wallets screen templateState =
  div
    [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0", "p-1" ] ] case screen of
    ContractsScreen contractStatus -> [ ContractAction <$> contractsScreen contractStatus ]
    WalletLibraryScreen -> [ walletLibraryScreen wallets ]
    TemplateScreen templateScreen -> [ TemplateAction <$> contractSetupScreen wallets templateScreen templateState ]

------------------------------------------------------------
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

------------------------------------------------------------
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
        Right action -> onClick_ action
    ]
    [ text label ]
