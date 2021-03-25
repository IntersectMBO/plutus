module Play.View (renderPlayState) where

import Prelude hiding (div)
import Contract.View (actionConfirmationCard, contractDetailsCard)
import ContractHome.View (contractsScreen)
import Css (applyWhen, classNames, hideWhen)
import Css as Css
import Data.Lens (preview, view)
import Data.Maybe (Maybe(..), isNothing)
import Data.String (take)
import Halogen.HTML (HTML, a, div, footer, header, img, main, nav, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href, src)
import Logo (marloweRunNavLogo, marloweRunNavLogoDark)
import MainFrame.Lenses (_card, _screen)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Semantics (PubKey)
import Material.Icons (Icon(..), icon_)
import Network.RemoteData (RemoteData)
import Play.Lenses (_contractsState, _currentSlot, _menuOpen, _selectedContract, _templateState, _walletDetails)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Prim.TypeError (class Warn, Text)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import WalletData.Lenses (_walletNickname)
import WalletData.Types (NewWalletDetails, WalletLibrary)
import WalletData.View (newWalletCard, walletDetailsCard, putdownWalletCard, walletLibraryScreen)

renderPlayState :: forall p. WalletLibrary -> NewWalletDetails -> Array ContractTemplate -> State -> HTML p Action
renderPlayState wallets newWalletDetails templates playState =
  let
    walletNickname = view (_walletDetails <<< _walletNickname) playState

    menuOpen = view _menuOpen playState
  in
    div
      [ classNames [ "grid", "h-full", "grid-rows-main" ] ]
      [ renderHeader walletNickname menuOpen
      , renderMain wallets newWalletDetails templates playState
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall p. PubKey -> Boolean -> HTML p Action
renderHeader walletNickname menuOpen =
  header
    [ classNames $ [ "relative", "flex", "justify-between", "items-center", "leading-none", "border-b", "border-gray", "py-3", "md:py-1", "px-4", "md:px-5pc" ] <> applyWhen menuOpen [ "border-0", "bg-black", "text-white" ] ]
    [ img
        [ classNames [ "w-16" ]
        , src if menuOpen then marloweRunNavLogoDark else marloweRunNavLogo
        ]
    , nav
        [ classNames [ "flex", "items-center" ] ]
        [ navigation (SetScreen ContractsScreen) Home "Home"
        , navigation (SetScreen WalletLibraryScreen) Contacts "Contacts"
        , a
            [ classNames [ "ml-6", "font-bold", "text-sm" ]
            , onClick_ $ ToggleCard PutdownWalletCard
            ]
            [ span
                [ classNames [ "md:hidden" ] ]
                [ icon_ Wallet ]
            , span
                [ classNames $ [ "hidden", "md:flex", "md:items-baseline" ] <> Css.button <> [ "bg-white" ] ]
                [ span
                    [ classNames $ [ "-m-1", "mr-2", "rounded-full", "text-white", "w-5", "h-5", "flex", "justify-center", "items-center", "uppercase" ] <> Css.bgBlueGradient ]
                    [ text $ take 1 walletNickname ]
                , text walletNickname
                ]
            ]
        , a
            [ classNames [ "ml-4", "md:hidden" ]
            , onClick_ ToggleMenu
            ]
            [ if menuOpen then icon_ Close else icon_ Menu ]
        ]
    ]
  where
  navigation action i label =
    a
      [ classNames [ "ml-6", "font-bold", "text-sm" ]
      , onClick_ action
      ]
      [ span
          [ classNames [ "md:hidden" ] ]
          [ icon_ i ]
      , span
          [ classNames [ "hidden", "md:inline" ] ]
          [ text label ]
      ]

------------------------------------------------------------
renderMain :: forall p. WalletLibrary -> NewWalletDetails -> Array ContractTemplate -> State -> HTML p Action
renderMain wallets newWalletDetails templates playState =
  let
    menuOpen = view _menuOpen playState

    screen = view _screen playState
  in
    main
      [ classNames [ "relative", "px-4", "md:px-5pc" ] ]
      [ renderMobileMenu menuOpen
      , renderCards wallets newWalletDetails templates playState
      , renderScreen wallets screen playState
      ]

renderMobileMenu :: forall p. Boolean -> HTML p Action
renderMobileMenu menuOpen =
  nav
    [ classNames $ [ "md:hidden", "absolute", "inset-0", "z-30", "bg-black", "text-white", "text-lg", "overflow-auto", "flex", "flex-col", "justify-between", "pt-8", "pb-4" ] <> hideWhen (not menuOpen) ]
    [ div
        [ classNames [ "flex", "flex-col" ] ]
        dashboardLinks
    , div
        [ classNames [ "flex", "flex-col" ] ]
        iohkLinks
    ]

renderCards :: forall p. WalletLibrary -> NewWalletDetails -> Array ContractTemplate -> State -> HTML p Action
renderCards wallets newWalletDetails templates playState =
  let
    currentWalletDetails = view _walletDetails playState

    mCard = view _card playState

    mSelectedContractState = preview _selectedContract playState

    cardClasses = case mCard of
      Just TemplateLibraryCard -> Css.largeCard false
      Just ContractCard -> Css.largeCard false
      Just _ -> Css.card false
      Nothing -> Css.card true

    hasCloseButton = case mCard of
      Just (ContractActionConfirmationCard _) -> false
      Just ContractSetupConfirmationCard -> false
      _ -> true

    closeButton =
      if hasCloseButton then
        [ a
            [ classNames [ "absolute", "top-4", "right-4" ]
            , onClick_ $ SetCard Nothing
            ]
            [ icon_ Close ]
        ]
      else
        []
  in
    div
      [ classNames $ Css.overlay $ isNothing mCard ]
      [ div
          [ classNames cardClasses ]
          $ closeButton
          <> case mCard of
              -- TODO: Should this be renamed to CreateContactCard?
              Just (CreateWalletCard mTokenName) -> [ newWalletCard wallets newWalletNickname newWalletContractId remoteDataPubKey mTokenName ]
              Just (ViewWalletCard walletDetails) -> [ walletDetailsCard walletDetails ]
              Just PutdownWalletCard -> [ putdownWalletCard currentWalletDetails ]
              Just TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard templates ]
              Just ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard ]
              -- FIXME: We need to pattern match on the Maybe because the selectedContractState
              --        could be Nothing. We could add the state as part of the view, but is not ideal
              --        Will have to rethink how to deal with this once the overall state is more mature.
              Just ContractCard -> case mSelectedContractState of
                Just contractState -> [ ContractAction <$> contractDetailsCard contractState ]
                Nothing -> []
              Just (ContractActionConfirmationCard action) -> case mSelectedContractState of
                Just contractState -> [ ContractAction <$> actionConfirmationCard contractState action ]
                Nothing -> []
              Nothing -> []
      ]

renderScreen :: forall p. WalletLibrary -> Screen -> State -> HTML p Action
renderScreen wallets screen playState =
  let
    currentSlot = view _currentSlot playState

    templateState = view _templateState playState

    contractsState = view _contractsState playState
  in
    div
      [ classNames [ "absolute", "top-0", "bottom-0", "left-0", "right-0", "overflow-auto", "z-0" ] ] case screen of
      ContractsScreen -> [ ContractHomeAction <$> contractsScreen contractsState ]
      WalletLibraryScreen -> [ walletLibraryScreen wallets ]
      TemplateScreen -> [ TemplateAction <$> contractSetupScreen wallets currentSlot templateState ]

------------------------------------------------------------
renderFooter :: forall p. HTML p Action
renderFooter =
  footer
    [ classNames [ "hidden", "md:flex", "py-2", "px-4", "md:px-5pc", "justify-between", "border-t", "border-gray", "text-sm" ] ]
    [ nav
        [ classNames [ "flex", "-ml-4" ] ] -- -ml-4 to offset the padding of the first link
        dashboardLinks
    , nav
        [ classNames [ "flex", "-mr-4" ] ] -- -mr-4 to offset the padding of the last link
        iohkLinks
    ]

------------------------------------------------------------
dashboardLinks :: forall p. Warn (Text "We need to add the dashboard links.") => Array (HTML p Action)
dashboardLinks =
  [ link "Market" ""
  , link "Docs" ""
  , link "Support" ""
  ]

iohkLinks :: forall p. Warn (Text "We need to add the IOHK links.") => Array (HTML p Action)
iohkLinks =
  [ link "marlowe.io" ""
  , link "cardano.org" "https://cardano.org"
  , link "iohk.io" "https://iohk.io"
  ]

link :: forall p. String -> String -> HTML p Action
link label url =
  a
    [ classNames [ "px-4", "py-2", "font-bold", "cursor-pointer" ]
    , href url
    ]
    [ text label ]
