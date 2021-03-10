module Play.View (renderPlayState) where

import Prelude hiding (div)
import Contract.View (contractDetailsCard)
import ContractHome.Lenses (_selectedContract)
import ContractHome.View (contractsScreen)
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
import Play.Lenses (_contractsState, _menuOpen, _templateState, _walletDetails)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Prim.TypeError (class Warn, Text)
import Servant.PureScript.Ajax (AjaxError)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import WalletData.Lenses (_nickname)
import WalletData.Types (Nickname, WalletLibrary)
import WalletData.View (newWalletCard, walletDetailsCard, putdownWalletCard, walletLibraryScreen)

renderPlayState :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> Array ContractTemplate -> State -> HTML p Action
renderPlayState wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState =
  let
    walletNickname = view (_walletDetails <<< _nickname) playState

    menuOpen = view _menuOpen playState
  in
    div
      [ classNames [ "grid", "h-full", "grid-rows-main" ] ]
      [ renderHeader walletNickname menuOpen
      , renderMain wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall p. PubKey -> Boolean -> HTML p Action
renderHeader walletNickname menuOpen =
  header
    [ classNames $ [ "relative", "flex", "justify-between", "border-b", "border-darkgray" ] <> applyWhen menuOpen [ "border-0", "bg-black", "text-white" ] ]
    [ h1
        [ classNames [ "text-xl", "font-bold", "px-4", "py-2" ] ]
        [ text "Marlowe" ]
    , nav
        [ classNames [ "flex" ] ]
        [ navigation (SetScreen ContractsScreen) Icon.home "Home"
        , navigation (SetScreen WalletLibraryScreen) Icon.contacts "Contacts"
        , navigation (ToggleCard PutdownWalletCard) Icon.wallet walletNickname
        , a
            [ classNames [ "p-2", "md:hidden" ]
            , onClick_ ToggleMenu
            ]
            [ if menuOpen then Icon.close else Icon.menu ]
        ]
    ]
  where
  navigation action icon label =
    a
      [ classNames [ "p-2" ]
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
renderMain :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> Array ContractTemplate -> State -> HTML p Action
renderMain wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState =
  let
    menuOpen = view _menuOpen playState

    screen = view _screen playState
  in
    main
      [ classNames [ "relative" ] ]
      [ renderMobileMenu menuOpen
      , renderCards wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState
      , renderScreen wallets screen playState
      ]

renderMobileMenu :: forall p. Boolean -> HTML p Action
renderMobileMenu menuOpen =
  nav
    [ classNames $ [ "md:hidden", "absolute", "top-0", "bottom-0", "left-0", "right-0", "z-10", "bg-black", "text-white", "overflow-auto", "flex", "flex-col", "justify-between" ] <> hideWhen (not menuOpen) ]
    [ div
        [ classNames [ "flex", "flex-col" ] ]
        $ [ link "Dashboard home" $ Right $ SetScreen ContractsScreen
          , link "Contacts" $ Right $ SetScreen WalletLibraryScreen
          ]
        <> dashboardLinks
    , div
        [ classNames [ "flex", "flex-col" ] ]
        iohkLinks
    ]

renderCards :: forall p. WalletLibrary -> Nickname -> String -> RemoteData AjaxError PubKey -> Array ContractTemplate -> State -> HTML p Action
renderCards wallets newWalletNickname newWalletContractId remoteDataPubKey templates playState =
  let
    currentWalletDetails = view _walletDetails playState

    mCard = view _card playState

    mSelectedContractState = view (_contractsState <<< _selectedContract) playState

    cardClasses = case mCard of
      Just TemplateLibraryCard -> Css.largeCard "bg-gray"
      Just ContractCard -> Css.largeCard "bg-grayblue"
      Just _ -> Css.card
      Nothing -> [ "hidden" ]
  in
    div
      [ classNames $ Css.cardWrapper $ isNothing mCard ]
      [ div
          [ classNames cardClasses ]
          [ div
              [ classNames [ "flex", "justify-end" ] ]
              [ a
                  [ classNames [ "p-2", "leading-none", "text-green" ]
                  , onClick_ $ SetCard Nothing
                  ]
                  [ Icon.close ]
              ]
          , div
              [ classNames [ "px-4", "pb-4" ] ]
              $ (flip foldMap mCard) \cardType -> case cardType of
                  CreateWalletCard -> [ newWalletCard wallets newWalletNickname newWalletContractId remoteDataPubKey ]
                  ViewWalletCard walletDetails -> [ walletDetailsCard walletDetails ]
                  PutdownWalletCard -> [ putdownWalletCard currentWalletDetails ]
                  TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard templates ]
                  NewContractForRoleCard -> []
                  ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard ]
                  -- FIXME: We need to pattern match on the Maybe because the selectedContractState
                  --        could be Nothing. We could add the state as part of the view, but is not ideal
                  --        Will have to rethink how to deal with this once the overall state is more mature.
                  ContractCard -> case mSelectedContractState of
                    Just contractState -> [ ContractAction <$> contractDetailsCard contractState ]
                    Nothing -> []
          ]
      ]

renderScreen :: forall p. WalletLibrary -> Screen -> State -> HTML p Action
renderScreen wallets screen playState =
  let
    templateState = view _templateState playState

    contractsState = view _contractsState playState
  in
    div
      [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0" ] ] case screen of
      ContractsScreen -> [ ContractHomeAction <$> contractsScreen contractsState ]
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
    [ classNames [ "p-4", "text-green", "hover:underline", "cursor-pointer" ]
    , case urlOrAction of
        Left url -> href url
        Right action -> onClick_ action
    ]
    [ text label ]
