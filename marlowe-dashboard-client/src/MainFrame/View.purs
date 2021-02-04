module MainFrame.View where

import Prelude hiding (div)
import Contract.View (renderContractSetup, renderRunningContract)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML, ClassName(ClassName))
import Halogen.HTML (a, button, div, div_, header, main, nav, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes)
import Library.View (renderContractLibrary, renderContractDetails)
import MainFrame.Types (Action(..), Card(..), ChildSlots, Screen(..), State, Overlay(..))
import Material.Icons as Icon
import Notifications.View (renderNotifications)
import Welcome.View (renderHome, renderContracts)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  div
    [ classes $ ClassName <$> [ "grid", "grid-rows-main", "h-full", "overflow-hidden" ] ]
    [ header
        [ classes $ ClassName <$> [ "relative" ] ]
        [ navbar state.overlay
        , menu state.overlay state.screen
        ]
    , main
        [ classes $ ClassName <$> [ "relative", "bg-lightblue", "text-blue" ] ]
        [ screen state
        , renderNotifications state.overlay state.notifications
        , card state
        ]
    ]

navbar :: forall m. MonadAff m => Maybe Overlay -> ComponentHTML Action ChildSlots m
navbar currentOverlay =
  nav
    [ classes $ ClassName <$> [ "sticky", "top-0", "flex" ] ]
    [ button
        [ classes $ ClassName <$> [ "btn", "text-midblue" ] ]
        [ Icon.image ]
    , nav
        [ classes $ ClassName <$> [ "flex", "flex-1", "justify-end" ] ]
        [ navButton Icon.notifications $ Just $ ToggleOverlay Notifications
        , navButton menuIcon $ Just $ ToggleOverlay Menu
        ]
    ]
  where
  menuIcon = if currentOverlay == Just Menu then Icon.close else Icon.menu

  navButton icon action =
    button
      [ classes $ ClassName <$> [ "btn", "text-green" ]
      , onClick $ const $ action
      ]
      [ icon ]

menu :: forall m. MonadAff m => Maybe Overlay -> Screen -> ComponentHTML Action ChildSlots m
menu currentOverlay currentScreen =
  div
    [ classes wrapperClasses ]
    [ nav
        [ classes $ ClassName <$> [ "bg-gray", "mx-0.5", "flex", "flex-col" ] ]
        [ menuItem "Home" (Just $ SetScreen Home) (currentScreen == Home)
        , menuItem "New Contract" (Just $ ToggleCard ContractLibrary) false
        , menuItem "Contracts" (Just $ SetScreen Contracts) (currentScreen == Contracts)
        , menuItem "Docs" Nothing false
        , menuItem "Support" Nothing false
        ]
    ]
  where
  wrapperClasses = ClassName <$> [ "absolute", "w-full", "z-20" ] <> if currentOverlay == Just Menu then [] else [ "hidden" ]

  menuItem label action active =
    a
      [ classes $ ClassName <$> [ "p-1", "hover:text-green", "hover:cursor-pointer" ] <> if active then [ "text-green" ] else []
      , onClick $ const action
      ]
      [ text label ]

screen :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
screen state =
  div
    [ classes $ ClassName <$> [ "h-full" ] ]
    [ case state.screen of
        Home -> renderHome state
        Contracts -> renderContracts state
        SetupContract contract -> renderContractSetup contract
    ]

card :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
card state =
  div
    [ classes $ ClassName <$> cardClasses ]
    [ button
        [ classes $ ClassName <$> [ "btn", "float-right", "text-green" ]
        , onClick $ const $ Just CloseCard
        ]
        [ Icon.close ]
    , case state.card of
        Just ContractLibrary -> renderContractLibrary state.contractTemplates
        Just (ContractDetails template) -> renderContractDetails template
        Just (RunningContract contract) -> renderRunningContract contract
        Nothing -> div_ []
    ]
  where
  cardClasses =
    [ "card" ]
      <> case state.card of
          Just _ -> []
          Nothing -> [ "hidden" ]

home :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
home state =
  div
    [ classes $ ClassName <$> [ "p-1" ] ]
    [ div
        [ classes $ ClassName <$> [ "flex", "justify-between" ] ]
        [ span
            []
            [ text $ "State: " <> if state.on then "Why would you do that?!" else "Everything is OK" ]
        , button
            [ classes $ ClassName <$> [ "btn", "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    , button
        [ classes $ ClassName <$> [ "btn", "absolute", "bottom-1", "left-1", "bg-blue", "text-white" ] ]
        [ Icon.help ]
    , button
        [ classes $ ClassName <$> [ "btn", "absolute", "bottom-1", "right-1", "bg-green", "text-white" ]
        , onClick $ const $ Just $ ToggleCard ContractLibrary
        ]
        [ Icon.libraryAdd ]
    ]
