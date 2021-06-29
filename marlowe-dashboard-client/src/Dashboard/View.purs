module Dashboard.View (renderDashboardState) where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _followerAppId, _mMarloweParams, _metadata, _nickname)
import Contract.State (currentStep, isContractClosed)
import Contract.Types (State) as Contract
import Contract.View (actionConfirmationCard, contractDetailsCard)
import Css (applyWhen, classNames, hideWhen, toggleWhen)
import Css as Css
import Dashboard.Lenses (_cards, _menuOpen, _remoteWalletInfo, _screen, _selectedContract, _status, _templateState, _walletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput)
import Dashboard.State (partitionContracts)
import Dashboard.Types (Action(..), Card(..), ContractStatus(..), Screen(..), State, PartitionedContracts)
import Data.Array (length)
import Data.Lens (preview, view, (^.))
import Data.Maybe (Maybe(..), maybe')
import Data.String (null, take)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, div, div_, footer, h2, header, img, main, nav, p_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href, id_, src)
import Humanize (humanizeDuration)
import Images (marloweRunNavLogo, marloweRunNavLogoDark)
import MainFrame.Types (ChildSlots)
import Marlowe.Execution.Lenses (_mNextTimeout)
import Marlowe.Extended (contractTypeInitials, contractTypeName)
import Marlowe.Semantics (PubKey, Slot)
import Marlowe.Slot (secondsDiff)
import Material.Icons (Icon(..), icon, icon_)
import Popper (Placement(..))
import Prim.TypeError (class Warn, Text)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))
import WalletData.Lenses (_assets, _walletNickname)
import WalletData.View (putdownWalletCard, saveWalletCard, walletDetailsCard, walletLibraryScreen)

renderDashboardState :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
renderDashboardState currentSlot state =
  let
    walletNickname = view (_walletDetails <<< _walletNickname) state

    menuOpen = view _menuOpen state

    screen = view _screen state

    cards = view _cards state
  in
    div
      [ classNames $ [ "grid", "h-full", "grid-rows-main" ] <> applyWhen menuOpen [ "bg-black" ] ]
      [ renderHeader walletNickname menuOpen
      , main
          [ classNames [ "relative", "px-4", "md:px-5pc" ] ]
          [ renderMobileMenu menuOpen
          , div_ $ renderCard currentSlot state <$> cards
          , renderScreen currentSlot state
          ]
      , renderFooter
      ]

------------------------------------------------------------
renderHeader :: forall m. MonadAff m => PubKey -> Boolean -> ComponentHTML Action ChildSlots m
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
            , id_ "dropWalletHeader"
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
        , tooltip "Drop wallet" (RefId "dropWalletHeader") Bottom
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

------------------------------------------------------------
renderScreen :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
renderScreen currentSlot state =
  let
    walletLibrary = view _walletLibrary state
  in
    div
      -- TODO: Revisit the overflow-auto... I think the scrolling should be set at the screen level and not here.
      --       this should have overflow-hidden to avoid the main div to occupy more space than available.
      [ classNames [ "absolute", "inset-0", "overflow-auto", "z-0" ] ]
      [ case state ^. _screen of
          ContractsScreen -> contractsScreen currentSlot state
          WalletLibraryScreen -> walletLibraryScreen walletLibrary
          TemplateScreen -> renderSubmodule _templateState TemplateAction (contractSetupScreen walletLibrary currentSlot) state
      ]

contractsScreen :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
contractsScreen currentSlot state =
  let
    buttonClasses = [ "w-40", "text-center" ]

    selectorButton true = Css.button <> [ "shadow", "bg-white" ] <> buttonClasses

    selectorButton false = Css.secondaryButton <> buttonClasses

    -- TODO: This is going to be called every second, if we have a performance issue
    -- see if we can use Lazy or to store the partition result in the state
    contracts = partitionContracts state.contracts

    viewSelector =
      div [ classNames [ "flex", "my-4", "justify-center", "px-4" ] ]
        [ a
            [ classNames $ (selectorButton $ state ^. _status == Running) <> [ "mr-4" ]
            , onClick_ $ SelectView Running
            , id_ "runningContractsFilter"
            ]
            [ text "What's running" ]
        , tooltip "View running contracts" (RefId "runningContractsFilter") Bottom
        , a
            [ classNames $ selectorButton $ state ^. _status == Completed
            , onClick_ $ SelectView Completed
            , id_ "completedContractsFilter"
            ]
            [ text "History" ]
        , tooltip "View completed contracts" (RefId "completedContractsFilter") Bottom
        ]
  in
    div
      [ classNames [ "pt-4", "flex", "flex-col", "h-full" ] ]
      [ h2
          [ classNames [ "font-semibold", "text-lg", "mb-4", "px-4", "md:px-5pc" ] ]
          [ text "Home" ]
      , viewSelector
      -- NOTE: This extra div is necesary to make the scroll only to work for the contract area.
      --       The parent flex with h-full and this element flex-grow makes the div to occupy the remaining
      --       vertical space.
      , div [ classNames [ "overflow-y-auto", "flex-grow", "px-4", "md:px-5pc" ] ]
          [ renderContracts currentSlot state contracts
          ]
      , a
          [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
          , onClick_ $ OpenCard TemplateLibraryCard
          ]
          [ text "Create" ]
      ]

renderContracts :: forall p. Slot -> State -> PartitionedContracts -> HTML p Action
renderContracts currentSlot { status: Running } { running }
  | length running == 0 = noContractsMessage "You have no running contracts. Tap create to begin."
  | otherwise = contractGrid currentSlot running

renderContracts currentSlot { status: Completed } { completed }
  | length completed == 0 = noContractsMessage "You have no completed contracts."
  | otherwise = contractGrid currentSlot completed

noContractsMessage :: forall p. String -> HTML p Action
noContractsMessage message =
  div
    [ classNames [ "h-full", "flex", "flex-col", "justify-center", "items-center" ] ]
    [ icon Contract [ "-mt-32", "text-big-icon", "text-gray" ]
    , p_ [ text message ]
    ]

contractGrid :: forall p. Slot -> Array Contract.State -> HTML p Action
contractGrid currentSlot contracts =
  div
    [ classNames [ "grid", "gap-4", "mb-4", "grid-cols-1", "sm:grid-cols-2-contract-home-card", "md:grid-cols-auto-fill-contract-home-card", "justify-center", "sm:justify-start" ] ]
    $ map (contractBox currentSlot) contracts

contractBox :: forall p. Slot -> Contract.State -> HTML p Action
contractBox currentSlot contractState =
  let
    nickname = contractState ^. _nickname

    mMarloweParams = contractState ^. _mMarloweParams

    metadata = contractState ^. _metadata

    contractType = contractTypeName metadata.contractType

    contractAcronym = contractTypeInitials metadata.contractType

    stepNumber = currentStep contractState + 1

    mNextTimeout = contractState ^. (_executionState <<< _mNextTimeout)

    contractInstanceId = contractState ^. _followerAppId

    timeoutStr =
      maybe'
        (\_ -> if isContractClosed contractState then "Contract closed" else "Timed out")
        (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
        mNextTimeout

    attributes = case mMarloweParams of
      Just _ ->
        -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
        [ classNames [ "flex", "flex-col", "cursor-pointer", "shadow-sm", "hover:shadow", "active:shadow-lg", "bg-white", "rounded", "overflow-hidden" ]
        , onClick_ $ OpenContract contractInstanceId
        ]
      -- in this case the box shouldn't be clickable
      Nothing -> [ classNames [ "flex", "flex-col", "shadow-sm", "bg-white", "rounded", "overflow-hidden" ] ]
  in
    div
      attributes
      -- TODO: This part is really similar to contractTitle in Template.View, see if it makes sense to factor a component out
      [ div
          [ classNames [ "flex", "px-4", "pt-4", "items-center" ] ]
          [ span [ classNames [ "text-2xl", "leading-none", "font-semibold" ] ] [ text contractAcronym ]
          , span [ classNames [ "flex-grow", "ml-2", "self-start", "text-xs", "uppercase" ] ] [ text contractType ]
          , icon ArrowRight [ "text-28px" ]
          ]
      , div
          [ classNames [ "flex-1", "px-4", "py-2", "text-lg" ] ]
          -- TODO: make (new) nicknames editable directly from here
          [ text if null nickname then "My new contract" else nickname ]
      , div
          [ classNames [ "bg-lightgray", "flex", "flex-col", "px-4", "py-2" ] ] case mMarloweParams of
          Nothing -> [ text "pending confirmation" ]
          _ ->
            [ span [ classNames [ "text-xs", "font-semibold" ] ] [ text $ "Step " <> show stepNumber <> ":" ]
            , span [ classNames [ "text-xl" ] ] [ text timeoutStr ]
            ]
      ]

------------------------------------------------------------
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
