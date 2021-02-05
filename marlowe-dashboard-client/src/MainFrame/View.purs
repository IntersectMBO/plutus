module MainFrame.View where

import Prelude hiding (div)
import Contact.View (renderContacts)
import Contract.View (renderContractSetup, renderContractDetails)
import Css (applyWhen, classNames, hideWhen)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (a, button, div, div_, header, main, nav, span, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Types (Action(..), Card(..), ChildSlots, ContractStatus(..), Screen(..), State, Overlay(..))
import Material.Icons as Icon
import Notifications.View (renderNotifications)
import Template.View (renderTemplateLibrary, renderTemplateDetails)
import Welcome.View (renderHome, renderContracts)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  div
    [ classNames [ "grid", "grid-rows-main", "h-full", "overflow-hidden" ] ]
    [ header
        [ classNames [ "relative" ] ]
        [ navbar state.overlay
        , menu state.overlay state.screen
        ]
    , main
        [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
        [ screen state
        , renderNotifications state.overlay state.notifications
        , card state
        ]
    ]

navbar :: forall m. MonadAff m => Maybe Overlay -> ComponentHTML Action ChildSlots m
navbar currentOverlay =
  nav
    [ classNames [ "sticky", "top-0", "flex" ] ]
    [ button
        [ classNames [ "btn", "text-midblue" ] ]
        [ Icon.image ]
    , nav
        [ classNames [ "flex", "flex-1", "justify-end" ] ]
        [ navButton Icon.notifications $ Just $ ToggleOverlay Notifications
        , navButton menuIcon $ Just $ ToggleOverlay Menu
        ]
    ]
  where
  menuIcon = if currentOverlay == Just Menu then Icon.close else Icon.menu

  navButton icon action =
    button
      [ classNames [ "btn", "text-green" ]
      , onClick $ const $ action
      ]
      [ icon ]

menu :: forall m. MonadAff m => Maybe Overlay -> Screen -> ComponentHTML Action ChildSlots m
menu currentOverlay currentScreen =
  div
    [ wrapperClassNames ]
    [ nav
        [ classNames [ "bg-gray", "mx-0.5", "flex", "flex-col" ] ]
        [ menuItem "Home" (Just $ SetScreen Home) (currentScreen == Home)
        , menuItem "Contacts" (Just $ SetScreen Contacts) (currentScreen == Contacts)
        , menuItem "New Contract" (Just $ ToggleCard TemplateLibrary) false
        , menuItem "Contracts" (Just $ SetScreen $ Contracts Running) isContracts
        , menuItem "Docs" Nothing false
        , menuItem "Support" Nothing false
        ]
    ]
  where
  wrapperClassNames = classNames $ [ "absolute", "w-full", "z-20" ] <> hideWhen (currentOverlay /= Just Menu)

  menuItem label action active =
    a
      [ classNames $ [ "p-1", "hover:text-green", "hover:cursor-pointer" ] <> applyWhen active "text-green"
      , onClick $ const action
      ]
      [ text label ]

  isContracts = case currentScreen of
    Contracts _ -> true
    _ -> false

screen :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
screen state =
  div
    [ classNames [ "h-full" ] ]
    [ case state.screen of
        Home -> renderHome state
        Contacts -> renderContacts state
        Contracts contractStatus -> renderContracts state.contracts contractStatus
        SetupContract contract -> renderContractSetup contract
    ]

card :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
card state =
  div
    [ classNames $ [ "card" ] <> hideWhen (state.card == Nothing) ]
    [ button
        [ classNames [ "btn", "float-right", "text-green" ]
        , onClick $ const $ Just CloseCard
        ]
        [ Icon.close ]
    , case state.card of
        Just TemplateLibrary -> renderTemplateLibrary state.templates
        Just (TemplateDetails contractTemplate) -> renderTemplateDetails contractTemplate
        Just (ContractDetails contractInstance) -> renderContractDetails contractInstance
        Nothing -> div_ []
    ]

home :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
home state =
  div
    [ classNames [ "p-1" ] ]
    [ div
        [ classNames [ "flex", "justify-between" ] ]
        [ span
            []
            [ text $ "State: " <> if state.on then "Why would you do that?!" else "Everything is OK" ]
        , button
            [ classNames [ "btn", "bg-blue", "text-white" ]
            , onClick $ const $ Just ClickedButton
            ]
            [ text "Click Me" ]
        ]
    , button
        [ classNames [ "btn", "absolute", "bottom-1", "left-1", "bg-blue", "text-white" ] ]
        [ Icon.help ]
    , button
        [ classNames [ "btn", "absolute", "bottom-1", "right-1", "bg-green", "text-white" ]
        , onClick $ const $ Just $ ToggleCard TemplateLibrary
        ]
        [ Icon.libraryAdd ]
    ]
