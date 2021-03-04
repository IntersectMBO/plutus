module Play.View (renderPlayState) where

import Prelude hiding (div)
import Contract.Types (State) as Contract
import Contract.View (contractsScreen, contractDetailsCard)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Either (Either(..))
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isNothing)
import Halogen.HTML (HTML, a, div, footer, h1, header, main, nav, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href)
import MainFrame.Lenses (_card, _screen)
import Marlowe.Extended (ContractTemplate)
import Marlowe.Semantics (PubKey)
import Material.Icons as Icon
import Network.RemoteData (RemoteData)
import Play.Lenses (_contractState, _menuOpen, _templateState, _walletDetails)
import Play.Types (Action(..), Card(..), ContractStatus(..), Screen(..), State)
import Prim.TypeError (class Warn, Text)
import Servant.PureScript.Ajax (AjaxError)
import Template.Types (State) as Template
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import WalletData.Lenses (_nickname)
import WalletData.Types (Nickname, WalletDetails, WalletLibrary)
import WalletData.View (newWalletCard, walletDetailsCard, putdownWalletCard, walletLibraryScreen)

renderPlayState :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> Array Template -> State -> HTML p Action
renderPlayState wallets newWalletDetails newWalletPubKey templates playState =
  let
    walletNickname = view (_walletDetails <<< _nickname) playState

    menuOpen = view _menuOpen playState
  in
    div
      [ classNames [ "grid", "h-full", "grid-rows-main" ] ]
      [ renderHeader walletNickname menuOpen
      , renderMain wallets newWalletDetails newWalletPubKey templates playState
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall p. PubKey -> Boolean -> HTML p Action
renderHeader walletNickname menuOpen =
  header
    [ classNames $ [ "relative", "flex", "justify-between", "border-b", "border-darkgray" ] <> applyWhen menuOpen [ "border-0", "bg-black", "text-white" ] ]
    [ h1
        [ classNames [ "text-xl", "font-bold", "px-1", "py-0.5" ] ]
        [ text "Marlowe" ]
    , nav
        [ classNames [ "flex" ] ]
        [ navigation (SetScreen $ ContractsScreen Running) Icon.home "Home"
        , navigation (SetScreen WalletLibraryScreen) Icon.contacts "Contacts"
        , navigation (ToggleCard PutdownWalletCard) Icon.wallet walletNickname
        , a
            [ classNames [ "p-0.5", "md:hidden" ]
            , onClick_ ToggleMenu
            ]
            [ if menuOpen then Icon.close else Icon.menu ]
        ]
    ]
  where
  navigation action icon label =
    a
      [ classNames [ "p-0.5" ]
      , onClick_ action
      ]
      [ span
          [ classNames [ "md:hidden" ] ]
          [ icon ]
      , span
          [ classNames [ "hidden", "md:inline" ] ]
          [ text label ]
      ]

------------------------------------------------------------
renderMain :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> Array Template -> State -> HTML p Action
renderMain wallets newWalletDetails newWalletPubKey templates playState =
  let
    walletDetails = view _walletDetails playState

    menuOpen = view _menuOpen playState

    screen = view _screen playState

    card = view _card playState

    templateState = view _templateState playState

    contractState = view _contractState playState
  in
    main
      [ classNames [ "relative" ] ]
      [ renderMobileMenu menuOpen
      , renderCards wallets newWalletDetails newWalletPubKey templates walletDetails card contractState
      , renderScreen wallets screen templateState
      ]

renderMobileMenu :: forall p. Boolean -> HTML p Action
renderMobileMenu menuOpen =
  nav
    [ classNames $ [ "md:hidden", "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-20", "bg-black", "text-white", "overflow-auto", "flex", "flex-col", "justify-between" ] <> hideWhen (not menuOpen) ]
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

renderCards :: forall p. WalletLibrary -> WalletDetails -> RemoteData AjaxError PubKey -> Array Template -> WalletDetails -> Maybe Card -> Contract.State -> HTML p Action
renderCards wallets newWalletDetails newWalletPubKey templates walletDetails card contractState =
  div
    [ classNames $ Css.cardWrapper $ isNothing card ]
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
                CreateWalletCard -> [ newWalletCard wallets newWalletDetails newWalletPubKey ]
                ViewWalletCard nickname contractId -> [ walletDetailsCard nickname contractId ]
                PutdownWalletCard -> [ putdownWalletCard walletDetails ]
                TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard templates ]
                NewContractForRoleCard -> []
                ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard ]
                ContractCard -> [ ContractAction <$> contractDetailsCard contractState ]
        ]
    ]
  where
  cardClasses = case card of
    Just TemplateLibraryCard -> Css.largeCard
    Just ContractCard -> Css.largeCard
    Just _ -> Css.card
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
    [ classNames [ "hidden", "md:flex", "justify-between", "border-t", "border-darkgray" ] ]
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
