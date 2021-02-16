module MainFrame.View where

import Prelude hiding (div)
import Contact.Lenses (_contacts, _newContactKey)
import Contact.View (renderContacts, renderContact, renderNewContact)
import Contract.View (renderContractSetup, renderContractDetails)
import Css (applyWhen, buttonClasses, classNames, hideWhen)
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.HTML (a, button, div, div_, h1, header, main, nav, span, text)
import Halogen.HTML.Events (onClick)
import MainFrame.Lenses (_contactState, _overlay, _screen, _templates)
import MainFrame.Types (Action(..), Card(..), ChildSlots, Overlay(..), Screen(..), State)
import Material.Icons as Icon
import Template.View (renderTemplateLibrary, renderTemplateDetails)
import Welcome.View (renderHome)

render :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
render state =
  let
    currentOverlay = view _overlay state

    currentScreen = view _screen state
  in
    div
      [ classNames [ "grid", "grid-rows-main", "h-full", "overflow-hidden" ] ]
      [ header
          [ classNames [ "relative" ] ]
          [ navbar currentOverlay
          , menu currentOverlay currentScreen
          ]
      , main
          [ classNames [ "relative", "bg-lightblue", "text-blue" ] ]
          [ screen state
          , card state
          ]
      ]

navbar :: forall m. MonadAff m => Maybe Overlay -> ComponentHTML Action ChildSlots m
navbar currentOverlay =
  nav
    [ classNames [ "sticky", "top-0", "flex", "items-center" ] ]
    [ button
        [ classNames $ buttonClasses <> [ "text-midblue" ] ]
        [ Icon.image ]
    , h1
        [ classNames [ "text-blue", "font-bold" ] ]
        [ text "Demo" ]
    , nav
        [ classNames [ "flex", "flex-1", "justify-end" ] ]
        [ navButton Icon.wallet Nothing
        , navButton menuIcon $ Just $ ToggleOverlay Menu
        , button
            [ classNames $ buttonClasses <> [ "bg-green", "text-white", "rounded-none", "flex", "items-center" ]
            , onClick $ const $ Just $ ToggleCard TemplateLibrary
            ]
            [ span
                [ classNames [ "px-0.5" ] ]
                [ text "New" ]
            , Icon.libraryAdd
            ]
        ]
    ]
  where
  menuIcon = if currentOverlay == Just Menu then Icon.close else Icon.menu

  navButton icon action =
    button
      [ classNames $ buttonClasses <> [ "text-green" ]
      , onClick $ const $ action
      ]
      [ icon ]

menu :: forall m. MonadAff m => Maybe Overlay -> Screen -> ComponentHTML Action ChildSlots m
menu currentOverlay currentScreen =
  div
    [ wrapperClassNames ]
    [ nav
        [ classNames [ "bg-gray", "mx-0.5", "mb-0.5", "flex", "flex-col", "justify-between" ] ]
        [ nav
            [ classNames [ "flex", "flex-col" ] ]
            [ menuItem "Dashboard home" $ Just $ SetScreen Home
            , menuItem "Contacts" $ Just $ SetScreen Contacts
            , menuItem "marlowe.io" Nothing
            , menuItem "Library" Nothing
            , menuItem "Docs" Nothing
            , menuItem "Support" Nothing
            ]
        , nav
            [ classNames [ "flex", "flex-col" ] ]
            [ menuItem "cardano.org" Nothing
            , menuItem "iohk.io" Nothing
            ]
        ]
    ]
  where
  wrapperClassNames = classNames $ [ "absolute", "w-full", "z-20" ] <> hideWhen (currentOverlay /= Just Menu)

  menuItem label action =
    a
      [ classNames $ [ "p-1", "text-green", "font-bold", "hover:cursor-pointer" ]
      , onClick $ const action
      ]
      [ text label ]

screen :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
screen state =
  let
    currentScreen = view _screen state

    contacts = view (_contactState <<< _contacts) state
  in
    div
      [ classNames [ "h-full" ] ]
      [ case currentScreen of
          Home -> renderHome state
          Contacts -> ContactAction <$> renderContacts contacts
          ViewContract contractInstance -> ContractAction <$> renderContractDetails contractInstance
          SetupContract contractTemplate -> ContractAction <$> renderContractSetup contractTemplate
      ]

card :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
card state =
  let
    contacts = view (_contactState <<< _contacts) state

    newContactKey = view (_contactState <<< _newContactKey) state

    templates = view _templates state
  in
    div
      [ classNames cardClasses ]
      [ button
          [ classNames $ buttonClasses <> [ "text-green", "absolute", "top-0", "right-0" ]
          , onClick $ const $ Just CloseCard
          ]
          [ Icon.close ]
      , case state.card of
          Just NewContact -> ContactAction <$> renderNewContact newContactKey contacts
          Just (EditContact contactKey) -> ContactAction <$> renderContact contactKey contacts
          Just TemplateLibrary -> renderTemplateLibrary templates
          Just (TemplateDetails contractTemplate) -> renderTemplateDetails contractTemplate
          Just (ContractDetails contractInstance) -> ContractAction <$> renderContractDetails contractInstance
          Nothing -> div_ []
      ]
  where
  cardClasses =
    [ "absolute"
    , "top-1"
    , "left-1"
    , "right-1"
    , "bottom-0"
    , "z-10"
    , "bg-white"
    , "mt-0"
    , "p-1"
    , "rounded-t-lg"
    , "transition-all"
    , "duration-400"
    , "transform"
    , "translate-y-0"
    ]
      <> applyWhen (state.card == Nothing) "translate-y-full"
