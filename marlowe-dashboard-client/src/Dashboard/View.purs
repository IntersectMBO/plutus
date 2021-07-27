module Dashboard.View
  ( dashboardScreen
  , dashboardCard
  ) where

import Prelude hiding (div)
import Contract.State (isContractClosed)
import Contract.Types (State) as Contract
import Contract.View (actionConfirmationCard, contractCard, contractScreen)
import Css as Css
import Dashboard.Lenses (_card, _cardOpen, _contractFilter, _contract, _menuOpen, _selectedContract, _selectedContractFollowerAppId, _templateState, _walletDetails, _walletDataState)
import Dashboard.Types (Action(..), Card(..), ContractFilter(..), State)
import Data.Lens (preview, view, (^.))
import Data.Map (Map, filter, isEmpty, toUnfoldable)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.String (take)
import Data.Tuple.Nested ((/\))
import Data.UUID (toString) as UUID
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Css (applyWhen, classNames)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, a, button, div, div_, footer, h2, h3, h4, header, img, input, label, main, nav, p, span, span_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Events.Extra (onClick_)
import Halogen.HTML.Properties (InputType(..), href, id_, readOnly, src, type_, value)
import Humanize (humanizeValue)
import Images (marloweRunNavLogo, marloweRunNavLogoDark)
import MainFrame.Types (ChildSlots)
import Marlowe.PAB (PlutusAppId)
import Marlowe.Semantics (PubKey, Slot)
import Material.Icons (Icon(..)) as Icon
import Material.Icons (icon, icon_)
import Popper (Placement(..))
import Prim.TypeError (class Warn, Text)
import Template.View (contractTemplateCard)
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))
import WalletData.Lenses (_assets, _companionAppId, _walletNickname, _walletLibrary)
import WalletData.State (adaToken, getAda)
import WalletData.Types (WalletDetails)
import WalletData.View (walletDataCard)

dashboardScreen :: forall m. MonadAff m => Slot -> State -> ComponentHTML Action ChildSlots m
dashboardScreen currentSlot state =
  let
    walletNickname = state ^. (_walletDetails <<< _walletNickname)

    menuOpen = state ^. _menuOpen

    card = state ^. _card

    cardOpen = state ^. _cardOpen

    contractFilter = state ^. _contractFilter

    selectedContractFollowerAppId = state ^. _selectedContractFollowerAppId

    selectedContract = preview _selectedContract state
  in
    div
      [ classNames
          $ [ "h-full", "grid", "grid-rows-auto-1fr-auto", "transition-all", "duration-500", "overflow-x-hidden" ]
          <> applyWhen cardOpen [ "lg:mr-sidebar" ]
      ]
      [ dashboardHeader walletNickname menuOpen
      , div [ classNames [ "relative" ] ] -- this wrapper is relative because the mobile menu is absolutely positioned inside it
          [ mobileMenu menuOpen
          , div [ classNames [ "h-full", "grid", "grid-rows-auto-1fr" ] ]
              [ dashboardBreadcrumb selectedContract
              , main
                  [ classNames [ "relative" ] ] case selectedContractFollowerAppId of
                  Just followerAppId -> [ renderSubmodule _selectedContract (ContractAction followerAppId) (contractScreen currentSlot) state ]
                  _ -> [ contractsScreen currentSlot state ]
              ]
          ]
      , dashboardFooter
      ]

dashboardCard ::
  forall m.
  MonadAff m =>
  Slot ->
  State ->
  ComponentHTML Action ChildSlots m
dashboardCard currentSlot state = case view _card state of
  Just card ->
    let
      cardOpen = state ^. _cardOpen

      walletLibrary = state ^. (_walletDataState <<< _walletLibrary)

      currentWallet = state ^. _walletDetails

      assets = currentWallet ^. _assets
    in
      div
        [ classNames $ Css.sidebarCardOverlay cardOpen ]
        [ div
            [ classNames $ Css.sidebarCard cardOpen ]
            $ [ a
                  [ classNames [ "absolute", "top-4", "right-4" ]
                  , onClick_ CloseCard
                  ]
                  [ icon_ Icon.Close ]
              , case card of
                  TutorialsCard -> tutorialsCard
                  CurrentWalletCard -> currentWalletCard currentWallet
                  WalletDataCard -> renderSubmodule _walletDataState WalletDataAction (walletDataCard currentWallet) state
                  ContractTemplateCard -> renderSubmodule _templateState TemplateAction (contractTemplateCard walletLibrary assets) state
                  ContractActionConfirmationCard followerAppId action -> renderSubmodule (_contract followerAppId) (ContractAction followerAppId) (actionConfirmationCard assets action) state
              ]
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
        [ classNames $ Css.maxWidthContainer <> [ "flex", "justify-between", "items-center", "leading-none", "py-3", "md:py-1" ] ]
        [ a
            [ onClick_ $ SelectContract Nothing ]
            [ img
                [ classNames [ "w-16", "md:hidden" ]
                , src if menuOpen then marloweRunNavLogoDark else marloweRunNavLogo
                ]
            -- ... and provide an alternative logo for wider screens that always has black text
            , img
                [ classNames [ "w-16", "hidden", "md:inline" ]
                , src marloweRunNavLogo
                ]
            ]
        , nav
            [ classNames [ "flex", "items-center" ] ]
            [ navigation (OpenCard WalletDataCard) Icon.Contacts "contactsHeader"
            , tooltip "Contacts" (RefId "contactsHeader") Bottom
            , navigation (OpenCard TutorialsCard) Icon.Tutorials "tutorialsHeader"
            , tooltip "Tutorials" (RefId "tutorialsHeader") Bottom
            , a
                [ classNames [ "ml-6", "font-bold", "text-sm" ]
                , id_ "currentWalletHeader"
                , onClick_ $ OpenCard CurrentWalletCard
                ]
                [ span
                    [ classNames $ [ "flex", "items-baseline", "gap-2", "bg-white", "rounded-lg", "p-4", "leading-none" ] ]
                    [ span
                        [ classNames $ [ "-m-1", "rounded-full", "text-white", "w-5", "h-5", "flex", "justify-center", "items-center", "uppercase", "font-semibold" ] <> Css.bgBlueGradient ]
                        [ text $ take 1 walletNickname ]
                    , span [ classNames [ "hidden", "md:inline", "truncate", "max-w-16" ] ] [ text walletNickname ]
                    ]
                ]
            , tooltip "Your wallet" (RefId "currentWalletHeader") Bottom
            , a
                [ classNames [ "ml-4", "md:hidden" ]
                , onClick_ ToggleMenu
                ]
                [ if menuOpen then icon_ Icon.Close else icon_ Icon.Menu ]
            ]
        ]
    ]
  where
  navigation action icon' refId =
    a
      [ classNames [ "ml-6", "font-bold", "text-sm" ]
      , id_ refId
      , onClick_ action
      ]
      [ icon_ icon' ]

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

dashboardBreadcrumb :: forall m. MonadAff m => (Maybe Contract.State) -> ComponentHTML Action ChildSlots m
dashboardBreadcrumb mSelectedContractState =
  div [ classNames [ "border-b", "border-gray" ] ]
    [ nav [ classNames $ Css.maxWidthContainer <> [ "flex", "gap-2", "py-2" ] ]
        $ [ a
              [ id_ "goToDashboard"
              , onClick \_ ->
                  if (isJust mSelectedContractState) then
                    Just $ SelectContract Nothing
                  else
                    Nothing
              , classNames
                  $ if (isJust mSelectedContractState) then
                      [ "text-lightpurple", "font-bold" ]
                    else
                      [ "cursor-default" ]
              ]
              [ text "Dashboard" ]
          ]
        <> case mSelectedContractState of
            Just { nickname } ->
              [ span [ classNames [ "font-semibold" ] ] [ text ">" ] -- FIXME: change > for an Icon
              , tooltip "Go to dashboard" (RefId "goToDashboard") Bottom
              , span_ [ text if nickname == mempty then "My new contract" else nickname ]
              ]
            Nothing -> []
    ]

dashboardFooter :: forall p. HTML p Action
dashboardFooter =
  footer
    [ classNames [ "hidden", "md:block", "border-t", "border-gray" ] ]
    [ div
        [ classNames $ Css.maxWidthContainer <> [ "flex", "justify-between", "py-2", "text-sm" ] ]
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
    contractFilter = view _contractFilter state
  in
    -- This convoluted combination of absolute and relative elements is the only way I could find
    -- to get the contract navigation element to be have a fixed position relative to a max-width
    -- container, at the same time as having the vertical scroll appear to be on the whole div.
    -- If not for the scroll, it could have just had position absolute (with a relative parent).
    -- And if not for the max width container, it could have just had position fixed.
    div
      [ classNames [ "h-full", "relative" ] ]
      [ div
          -- overflow-x here can occur when the sidebar is open
          [ classNames [ "absolute", "z-10", "inset-0", "h-full", "overflow-y-auto", "overflow-x-hidden" ] ]
          [ div
              [ classNames $ Css.maxWidthContainer <> [ "relative", "h-full" ] ]
              [ contractCards currentSlot state ]
          ]
      , div
          [ classNames [ "absolute", "inset-0" ] ]
          [ div
              [ classNames $ Css.maxWidthContainer <> [ "relative", "h-full" ] ]
              [ contractNavigation contractFilter ]
          ]
      ]

contractNavigation :: forall m. MonadAff m => ContractFilter -> ComponentHTML Action ChildSlots m
contractNavigation contractFilter =
  let
    navClasses = [ "inline-flex", "gap-4", "overflow-hidden", "px-3", "lg:px-0", "lg:py-3", "lg:flex-col", "bg-white", "rounded", "shadow" ]

    navItemClasses active = [ "leading-none", "pt-2+2px", "pb-2", "border-b-2", "lg:py-0", "lg:pr-2+2px", "lg:pl-2", "lg:border-b-0", "lg:border-l-2", "border-transparent" ] <> applyWhen active [ "border-black" ]
  in
    div
      [ classNames [ "absolute", "z-20", "left-4", "bottom-4", "right-4", "lg:right-auto", "lg:top-0", "grid", "grid-cols-1fr-auto-1fr", "lg:grid-cols-none", "lg:grid-rows-1fr-auto-1fr" ] ]
      [ div
          [ classNames [ "row-start-1", "col-start-2", "lg:row-start-2", "lg:col-start-1" ] ]
          [ nav
              [ classNames navClasses ]
              [ a
                  [ classNames $ navItemClasses $ contractFilter == Running
                  , onClick_ $ SetContractFilter Running
                  , id_ "runningContractsFilter"
                  ]
                  [ icon_ Icon.Running ]
              , tooltip "Running contracts" (RefId "runningContractsFilter") Right
              , a
                  [ classNames $ navItemClasses $ contractFilter == Completed
                  , onClick_ $ SetContractFilter Completed
                  , id_ "completedContractsFilter"
                  ]
                  [ icon_ Icon.History ]
              , tooltip "Completed contracts" (RefId "completedContractsFilter") Right
              , a
                  [ classNames $ navItemClasses false
                  , onClick_ $ OpenCard ContractTemplateCard
                  , id_ "newContractButton"
                  ]
                  [ icon Icon.AddBox [ "text-purple" ] ]
              , tooltip "Create a new contract" (RefId "newContractButton") Right
              ]
          ]
      , div
          [ classNames [ "row-start-1", "col-start-1", "lg:row-start-3", "lg:self-end" ] ]
          [ nav
              [ classNames navClasses ]
              [ a
                  [ classNames $ navItemClasses false
                  , onClick_ $ OpenCard TutorialsCard
                  , id_ "tutorialsButton"
                  ]
                  [ icon Icon.Help [ "text-purple" ] ]
              , tooltip "Tutorials" (RefId "tutorialsButton") Right
              ]
          ]
      ]

contractCards :: forall p. Slot -> State -> HTML p Action
contractCards currentSlot { contractFilter: Running, contracts } =
  let
    runningContracts = filter (not isContractClosed) contracts
  in
    if isEmpty runningContracts then
      noContractsMessage Running
    else
      contractGrid currentSlot Running runningContracts

contractCards currentSlot { contractFilter: Completed, contracts } =
  let
    completedContracts = filter isContractClosed contracts
  in
    if isEmpty completedContracts then
      noContractsMessage Completed
    else
      contractGrid currentSlot Completed completedContracts

noContractsMessage :: forall p. ContractFilter -> HTML p Action
noContractsMessage contractFilter =
  div
    [ classNames [ "h-full", "flex", "flex-col", "justify-center", "items-center" ] ]
    $ [ icon Icon.Contract [ "text-big-icon", "text-gray" ] ]
    <> case contractFilter of
        Running ->
          [ p
              [ classNames [ "text-lg", "font-semibold", "mb-2" ] ]
              [ text "You have no running contracts." ]
          , p
              [ classNames [ "text-lg", "mb-4" ] ]
              [ text "Choose a template to begin." ]
          , button
              [ classNames Css.primaryButton
              , onClick_ $ OpenCard ContractTemplateCard
              ]
              [ text "Choose a template" ]
          ]
        Completed ->
          [ p
              [ classNames [ "text-lg", "font-semibold", "mb-2" ] ]
              [ text "You have no completed contracts." ]
          ]

contractGrid :: forall p. Slot -> ContractFilter -> Map PlutusAppId Contract.State -> HTML p Action
contractGrid currentSlot contractFilter contracts =
  div
    [ classNames [ "grid", "pt-4", "pb-20", "lg:pb-4", "gap-8", "auto-rows-min", "mx-auto", "max-w-contracts-grid-sm", "md:max-w-none", "md:w-contracts-grid-md", "md:grid-cols-2", "lg:w-contracts-grid-lg", "lg:grid-cols-3" ] ]
    $ case contractFilter of
        Running -> [ newContractCard ]
        Completed -> []
    <> (dashboardContractCard <$> toUnfoldable contracts)
  where
  newContractCard =
    a
      [ classNames [ "hidden", "md:flex", "flex-col", "justify-center", "items-center", "rounded", "border-2", "border-darkgray", "border-dashed", "p-4" ]
      , onClick_ $ OpenCard ContractTemplateCard
      ]
      [ icon_ Icon.AddCircle
      , span_ [ text "New smart contract from template" ]
      ]

  dashboardContractCard (followerAppId /\ contractState) = ContractAction followerAppId <$> contractCard currentSlot contractState

-- TODO: waiting new design for this from Russ
currentWalletCard :: forall p. WalletDetails -> HTML p Action
currentWalletCard walletDetails =
  let
    walletNickname = view _walletNickname walletDetails

    companionAppId = view _companionAppId walletDetails

    assets = view _assets walletDetails
  in
    div [ classNames [ "p-5", "pb-6", "md:pb-8" ] ]
      [ h3
          [ classNames [ "font-semibold", "mb-4", "truncate", "w-11/12" ] ]
          [ text $ "Wallet " <> walletNickname ]
      , div
          [ classNames Css.hasNestedLabel ]
          [ label
              [ classNames Css.nestedLabel ]
              [ text "Wallet ID" ]
          , input
              [ type_ InputText
              , classNames $ Css.input true <> [ "mb-4" ]
              , value $ UUID.toString $ unwrap companionAppId
              , readOnly true
              ]
          ]
      , div
          [ classNames [ "mb-4" ] ]
          [ h4
              [ classNames [ "font-semibold" ] ]
              [ text "Balance:" ]
          , p
              [ classNames Css.funds ]
              [ text $ humanizeValue adaToken $ getAda assets ]
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
              , onClick_ PutdownWallet
              ]
              [ text "Drop wallet" ]
          ]
      ]

-- FIXME: add a proper tutorials card (possibly a whole tutorials module)
tutorialsCard :: forall p. HTML p Action
tutorialsCard =
  div
    [ classNames [ "p-4" ] ]
    [ h2
        [ classNames [ "font-semibold", "text-lg", "mb-4" ] ]
        [ text "Tutorials" ]
    ]
