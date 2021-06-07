module Play.View (renderPlayState) where

import Prelude hiding (div)
import Contract.View (actionConfirmationCard, contractDetailsCard)
import ContractHome.View (contractsScreen)
import Css (applyWhen, classNames, hideWhen, toggleWhen)
import Css as Css
import Data.Lens (preview, view)
import Data.Maybe (Maybe(..))
import Data.String (take)
import Halogen.HTML (HTML, a, div, div_, footer, header, img, main, nav, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href, src)
import Images (marloweRunNavLogo, marloweRunNavLogoDark)
import Marlowe.Semantics (PubKey, Slot)
import Material.Icons (Icon(..), icon_)
import Play.Lenses (_cards, _contractsState, _menuOpen, _walletIdInput, _walletNicknameInput, _remoteWalletInfo, _screen, _selectedContract, _templateState, _walletDetails, _walletLibrary)
import Play.Types (Action(..), Card(..), Screen(..), State)
import Prim.TypeError (class Warn, Text)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import WalletData.Lenses (_assets, _walletNickname)
import WalletData.View (putdownWalletCard, saveWalletCard, walletDetailsCard, walletLibraryScreen)

renderPlayState :: forall p. Slot -> State -> HTML p Action
renderPlayState currentSlot state =
  let
    walletNickname = view (_walletDetails <<< _walletNickname) state

    menuOpen = view _menuOpen state
  in
    div
      [ classNames $ [ "grid", "h-full", "grid-rows-main" ] <> applyWhen menuOpen [ "bg-black" ] ]
      [ renderHeader walletNickname menuOpen
      , renderMain currentSlot state
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall p. PubKey -> Boolean -> HTML p Action
renderHeader walletNickname menuOpen =
  header
    [ classNames
        $ [ "relative", "flex", "justify-between", "items-center", "leading-none", "py-3", "md:py-1", "px-4", "md:px-5pc" ]
        -- in case the menu is open when the user makes their window wider, we make sure the menuOpen styles only apply on small screens ...
        
        <> toggleWhen menuOpen [ "border-0", "bg-black", "text-white", "md:border-b", "md:bg-transparent", "md:text-black" ] [ "border-b", "border-gray" ]
    ]
    [ img
        [ classNames [ "w-16", "md:hidden" ]
        , src if menuOpen then marloweRunNavLogoDark else marloweRunNavLogo
        ]
    -- ... and provide an alternative logo for wider screens that always has black text
    , img
        [ classNames [ "w-16", "hidden", "md:inline" ]
        , src marloweRunNavLogo
        ]
    , nav
        [ classNames [ "flex", "items-center" ] ]
        [ navigation (SetScreen ContractsScreen) Home "Home"
        , navigation (SetScreen WalletLibraryScreen) Contacts "Contacts"
        , a
            [ classNames [ "ml-6", "font-bold", "text-sm" ]
            , onClick_ $ OpenCard PutdownWalletCard
            ]
            [ span
                [ classNames [ "md:hidden" ] ]
                [ icon_ Wallet ]
            , span
                [ classNames $ [ "hidden", "md:flex", "md:items-baseline" ] <> Css.button <> [ "bg-white" ] ]
                [ span
                    [ classNames $ [ "-m-1", "mr-2", "rounded-full", "text-white", "w-5", "h-5", "flex", "justify-center", "items-center", "uppercase", "font-semibold" ] <> Css.bgBlueGradient ]
                    [ text $ take 1 walletNickname ]
                , span [ classNames [ "truncate", "max-w-16" ] ] [ text walletNickname ]
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
renderMain :: forall p. Slot -> State -> HTML p Action
renderMain currentSlot state =
  let
    menuOpen = view _menuOpen state

    screen = view _screen state

    cards = view _cards state
  in
    main
      [ classNames [ "relative", "px-4", "md:px-5pc" ] ]
      [ renderMobileMenu menuOpen
      , div_ $ renderCard currentSlot state <$> cards
      , renderScreen currentSlot state
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

renderCard :: forall p. Slot -> State -> Card -> HTML p Action
renderCard currentSlot state card =
  let
    walletLibrary = view _walletLibrary state

    currentWalletDetails = view _walletDetails state

    assets = view _assets currentWalletDetails

    walletNicknameInput = view _walletNicknameInput state

    walletIdInput = view _walletIdInput state

    remoteWalletInfo = view _remoteWalletInfo state

    mSelectedContractState = preview _selectedContract state

    cardClasses = case card of
      TemplateLibraryCard -> Css.largeCard false
      ContractCard -> Css.largeCard false
      _ -> Css.card false

    hasCloseButton = case card of
      (ContractActionConfirmationCard _) -> false
      ContractSetupConfirmationCard -> false
      _ -> true

    closeButton =
      if hasCloseButton then
        [ a
            [ classNames [ "absolute", "top-4", "right-4" ]
            , onClick_ $ CloseCard card
            ]
            [ icon_ Close ]
        ]
      else
        []
  in
    div
      [ classNames $ Css.overlay false ]
      [ div
          [ classNames cardClasses ]
          $ closeButton
          <> case card of
              SaveWalletCard mTokenName -> [ saveWalletCard walletLibrary walletNicknameInput walletIdInput remoteWalletInfo mTokenName ]
              ViewWalletCard walletDetails -> [ walletDetailsCard walletDetails ]
              PutdownWalletCard -> [ putdownWalletCard currentWalletDetails ]
              TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard ]
              ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard assets ]
              -- FIXME: We need to pattern match on the Maybe because the selectedContractState
              --        could be Nothing. We could add the state as part of the view, but is not ideal
              --        Will have to rethink how to deal with this once the overall state is more mature.
              ContractCard -> case mSelectedContractState of
                Just contractState -> [ ContractAction <$> contractDetailsCard currentSlot contractState ]
                Nothing -> []
              ContractActionConfirmationCard action -> case mSelectedContractState of
                Just contractState -> [ ContractAction <$> actionConfirmationCard assets contractState action ]
                Nothing -> []
      ]

renderScreen :: forall p. Slot -> State -> HTML p Action
renderScreen currentSlot state =
  let
    walletLibrary = view _walletLibrary state

    screen = view _screen state

    templateState = view _templateState state

    contractsState = view _contractsState state
  in
    div
      -- TODO: Revisit the overflow-auto... I think the scrolling should be set at the screen level and not here.
      --       this should have overflow-hidden to avoid the main div to occupy more space than available.
      [ classNames [ "absolute", "inset-0", "overflow-auto", "z-0" ] ] case screen of
      ContractsScreen -> [ ContractHomeAction <$> contractsScreen currentSlot contractsState ]
      WalletLibraryScreen -> [ walletLibraryScreen walletLibrary ]
      TemplateScreen -> [ TemplateAction <$> contractSetupScreen walletLibrary currentSlot templateState ]

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
  -- FIXME: Add link to Docs
  [ link "Docs" ""
  , link "marlowe-finance.io" "https://marlowe-finance.io"
  , link "play.marlowe-finance.io" "https://play.marlowe-finance.io"
  {- disabled for phase 1, link "Market" ""
  , link "Support" "" -}
  ]

iohkLinks :: forall p. Array (HTML p Action)
iohkLinks =
  [ link "cardano.org" "https://cardano.org"
  , link "iohk.io" "https://iohk.io"
  ]

link :: forall p. String -> String -> HTML p Action
link label url =
  a
    [ classNames [ "px-4", "py-2", "font-bold", "cursor-pointer" ]
    , href url
    ]
    [ text label ]
