module Dashboard.View
  ( dashboardScreen
  , dashboardCard
  ) where

import Prelude hiding (div)
import Contract.Lenses (_followerAppId, _mMarloweParams, _metadata)
import Contract.Types (State) as Contract
import Contract.View (actionConfirmationCard, contractDetailsCard, contractInnerBox)
import Css as Css
import Dashboard.Lenses (_card, _cardOpen, _menuOpen, _remoteWalletInfo, _selectedContract, _status, _templateState, _walletDetails, _walletIdInput, _walletLibrary, _walletNicknameInput)
import Dashboard.State (partitionContracts)
import Dashboard.Types (Action(..), Card(..), ContractStatus(..), State, PartitionedContracts)
import Data.Array (length)
import Data.Lens (preview, view, (^.))
import Data.Maybe (Maybe(..), isJust)
import Data.String (take)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (applyWhen, classNames)
import Halogen.HTML (HTML, a, div, div_, footer, header, img, main, nav, p_, span, span_, text)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (href, id_, src)
import Images (marloweRunNavLogo, marloweRunNavLogoDark)
import MainFrame.Types (ChildSlots)
import Marlowe.Extended (contractTypeInitials, contractTypeName)
import Marlowe.Semantics (PubKey, Slot)
import Material.Icons (Icon(..), icon, icon_)
import Popper (Placement(..))
import Prim.TypeError (class Warn, Text)
import Template.View (contractSetupConfirmationCard, contractSetupScreen, templateLibraryCard)
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))
import WalletData.Lenses (_assets, _walletNickname)
import WalletData.View (putdownWalletCard, saveWalletCard, walletDetailsCard, walletLibraryScreen)

dashboardScreen :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
dashboardScreen currentSlot state =
  let
    walletNickname = view (_walletDetails <<< _walletNickname) state

    menuOpen = view _menuOpen state

    card = view _card state

    cardOpen = view _cardOpen state

    mSelectedContractState = preview _selectedContract state
  in
    div
      [ classNames
          $ [ "h-full", "grid", "grid-rows-dashboard-outer", "transition-all", "duration-500" ]
          <> applyWhen cardOpen [ "lg:mr-sidebar" ]
      ]
      [ dashboardHeader walletNickname menuOpen
      , div [ classNames [ "relative" ] ] -- this wrapper is relative because the mobile menu is absolutely positioned inside it
          [ mobileMenu menuOpen
          , div [ classNames [ "h-full", "grid", "grid-rows-dashboard-inner" ] ]
              [ dashboardBreadcrumb mSelectedContractState
              , main
                  [ classNames $ [ "w-full" ] <> if isJust mSelectedContractState then [] else Css.container ] case mSelectedContractState of
                  Just contractState -> [ ContractAction <$> contractDetailsCard currentSlot contractState ]
                  Nothing -> [ contractsScreen currentSlot state ]
              ]
          ]
      , dashboardFooter
      ]

dashboardCard :: forall p. Slot -> State -> HTML p Action
dashboardCard currentSlot state = case view _card state of
  Just card ->
    let
      cardOpen = view _cardOpen state

      walletLibrary = view _walletLibrary state

      currentWalletDetails = view _walletDetails state

      assets = view _assets currentWalletDetails

      walletNicknameInput = view _walletNicknameInput state

      walletIdInput = view _walletIdInput state

      remoteWalletInfo = view _remoteWalletInfo state

      mSelectedContractState = preview _selectedContract state

      templateState = view _templateState state
    in
      div
        [ classNames $ Css.sidebarCardOverlay cardOpen ]
        [ div
            [ classNames $ Css.sidebarCard cardOpen ]
            $ [ a
                  [ classNames [ "absolute", "top-4", "right-4" ]
                  , onClick_ CloseCard
                  ]
                  [ icon_ Close ]
              ]
            <> case card of
                SaveWalletCard mTokenName -> [ saveWalletCard walletLibrary walletNicknameInput walletIdInput remoteWalletInfo mTokenName ]
                ViewWalletCard walletDetails -> [ walletDetailsCard walletDetails ]
                PutdownWalletCard -> [ putdownWalletCard currentWalletDetails ]
                WalletLibraryCard -> [ walletLibraryScreen walletLibrary ]
                TemplateLibraryCard -> [ TemplateAction <$> templateLibraryCard ]
                ContractSetupCard -> [ TemplateAction <$> contractSetupScreen walletLibrary currentSlot templateState ]
                ContractSetupConfirmationCard -> [ TemplateAction <$> contractSetupConfirmationCard assets ]
                ContractActionConfirmationCard action -> case mSelectedContractState of
                  Just contractState -> [ ContractAction <$> actionConfirmationCard assets contractState action ]
                  Nothing -> []
        ]
  Nothing -> div_ []

------------------------------------------------------------
dashboardHeader :: forall m. MonadAff m => PubKey -> Boolean -> ComponentHTML Action ChildSlots m
dashboardHeader walletNickname menuOpen =
  header
    [ classNames
        $ [ "relative", "border-gray", "transition-colors", "duration-200" ]
        <> if menuOpen then [ "border-0", "bg-black", "text-white", "md:border-b", "md:bg-transparent", "md:text-black" ] else [ "border-b", "text-black" ]
    -- ^ in case the menu is open when the user makes their window wider, we make sure the menuOpen styles only apply on small screens ...
    ]
    [ div
        [ classNames $ Css.container <> [ "flex", "justify-between", "items-center", "leading-none", "py-3", "md:py-1" ] ]
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
            [ navigation (SelectContract Nothing) Home "Home"
            , navigation (OpenCard WalletLibraryCard) Contacts "Contacts"
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

mobileMenu :: forall p. Boolean -> HTML p Action
mobileMenu menuOpen =
  nav
    [ classNames
        $ [ "md:hidden", "absolute", "inset-0", "z-30", "bg-black", "text-white", "text-lg", "overflow-auto", "flex", "flex-col", "justify-between", "pt-8", "pb-4", "transition-all", "duration-200" ]
        <> if menuOpen then [ "opacity-100" ] else [ "opacity-0", "pointer-events-none" ]
    ]
    [ div
        [ classNames [ "flex", "flex-col" ] ]
        dashboardLinks
    , div
        [ classNames [ "flex", "flex-col" ] ]
        iohkLinks
    ]

dashboardBreadcrumb :: forall p. (Maybe Contract.State) -> HTML p Action
dashboardBreadcrumb mSelectedContractState =
  div [ classNames [ "border-b", "border-gray" ] ]
    [ nav [ classNames $ Css.container <> [ "flex", "gap-2", "py-2" ] ]
        $ [ a [ onClick_ $ SelectContract Nothing ] [ text "Dashboard" ] ]
        <> case mSelectedContractState of
            Just { nickname } ->
              [ span_ [ text ">" ]
              , span_ [ text nickname ]
              ]
            Nothing -> []
    ]

dashboardFooter :: forall p. HTML p Action
dashboardFooter =
  footer
    [ classNames [ "hidden", "md:block", "border-t", "border-gray" ] ]
    [ div
        [ classNames $ Css.container <> [ "flex", "justify-between", "py-2", "text-sm" ] ]
        [ nav
            [ classNames [ "flex", "-ml-4" ] ] -- -ml-4 to offset the padding of the first link
            dashboardLinks
        , nav
            [ classNames [ "flex", "-mr-4" ] ] -- -mr-4 to offset the padding of the last link
            iohkLinks
        ]
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
      [ viewSelector
      -- NOTE: This extra div is necesary to make the scroll only to work for the contract area.
      --       The parent flex with h-full and this element flex-grow makes the div to occupy the remaining
      --       vertical space.
      , div [ classNames [ "overflow-y-auto", "flex-grow", "px-4" ] ]
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
    mMarloweParams = contractState ^. _mMarloweParams

    metadata = contractState ^. _metadata

    contractInstanceId = contractState ^. _followerAppId

    attributes = case mMarloweParams of
      Just _ ->
        -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
        [ classNames [ "flex", "flex-col", "cursor-pointer", "shadow-sm", "hover:shadow", "active:shadow-lg", "bg-white", "rounded", "overflow-hidden" ]
        , onClick_ $ SelectContract $ Just contractInstanceId
        ]
      -- in this case the box shouldn't be clickable
      Nothing -> [ classNames [ "flex", "flex-col", "shadow-sm", "bg-white", "rounded", "overflow-hidden" ] ]
  in
    div
      attributes
      -- TODO: This part is really similar to contractTitle in Template.View, see if it makes sense to factor a component out
      [ div
          [ classNames [ "flex", "px-4", "pt-4", "items-center" ] ]
          [ span [ classNames [ "text-2xl", "leading-none", "font-semibold" ] ] [ text $ contractTypeInitials metadata.contractType ]
          , span [ classNames [ "flex-grow", "ml-2", "self-start", "text-xs", "uppercase" ] ] [ text $ contractTypeName metadata.contractType ]
          , icon ArrowRight [ "text-28px" ]
          ]
      , ContractAction <$> contractInnerBox currentSlot contractState
      ]
