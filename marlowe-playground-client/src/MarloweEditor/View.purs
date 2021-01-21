module MarloweEditor.View where

import Prelude hiding (div)
import BottomPanel.Types (_showBottomPanel)
import BottomPanel.Types as BottomPanel
import BottomPanel.View as BottomPanel
import Data.Array (length)
import Data.Array as Array
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens ((^.))
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (codeEditor, group)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, button, div, div_, option, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled, title)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe.Monaco as MM
import MarloweEditor.BottomPanel (panelContents)
import MarloweEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _editorErrors, _editorWarnings, _keybindings, contractHasErrors, contractHasHoles)
import Monaco (getModel, setValue) as Monaco
import Prim.TypeError (class Warn, Text)
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes [ codeEditor ] ]
            [ marloweEditor state ]
        ]
    , renderSubmodule _bottomPanelState BottomPanelAction (BottomPanel.render panelTitles wrapBottomPanelContents) state
    ]
  where
  panelTitles =
    [ { title: "Static Analysis", view: StaticAnalysisView, classes: [] }
    , { title: warningsTitle, view: MarloweWarningsView, classes: [] }
    , { title: errorsTitle, view: MarloweErrorsView, classes: [] }
    ]

  withCount str arry = str <> if Array.null arry then "" else " (" <> show (length arry) <> ")"

  warningsTitle = withCount "Warnings" $ state ^. _editorWarnings

  errorsTitle = withCount "Errors" $ state ^. _editorErrors

  wrapBottomPanelContents panelView = BottomPanel.PanelAction <$> panelContents state panelView

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , viewAsBlocklyButton state
    , sendToSimulatorButton state
    ]

sendToSimulatorButton ::
  forall p.
  Warn (Text "Create a custom tooltip element") =>
  State ->
  HTML p Action
sendToSimulatorButton state =
  button
    ( [ onClick $ const $ Just SendToSimulator
      , disabled disabled'
      ]
        <> disabledTooltip
    )
    [ text "Send To Simulator" ]
  where
  disabled' = contractHasErrors state || contractHasHoles state

  disabledTooltip =
    if disabled' then
      {-
        TODO: The title property generates a native tooltip in the browser, but it takes a couple
        of seconds to appear, we should ask for a design and then implement a custom tooltip element.
      -}
      [ title "A contract can only be sent to the simulator if it has no errors and no holes"
      ]
    else
      []

viewAsBlocklyButton :: forall p. State -> HTML p Action
viewAsBlocklyButton state =
  button
    ( [ onClick $ const $ Just ViewAsBlockly
      , disabled disabled'
      ]
        <> disabledTooltip
    )
    [ text "View as blocks" ]
  where
  -- We only enable this button when the contract is valid, even if it has holes
  disabled' = contractHasErrors state

  disabledTooltip =
    if disabled' then
      [ title "We can't send the contract to blockly while it has errors"
      ]
    else
      []

editorOptions :: forall p. State -> HTML p Action
editorOptions state =
  div [ class_ (ClassName "editor-options") ]
    [ select
        [ HTML.id_ "editor-options"
        , class_ (ClassName "dropdown-header")
        , HTML.value $ show $ state ^. _keybindings
        , onSelectedIndexChange (\idx -> ChangeKeyBindings <$> toEnum idx)
        ]
        (map keybindingItem (upFromIncluding bottom))
    ]
  where
  keybindingItem item =
    if state ^. _keybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

marloweEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
marloweEditor state = slot _marloweEditorPageSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor =
    liftEffect do
      -- FIXME we shouldn't access local storage from the view
      mContents <- LocalStorage.getItem StaticData.marloweBufferLocalStorageKey
      let
        contents = fromMaybe HE.escrow mContents
      model <- Monaco.getModel editor
      Monaco.setValue model contents

  component = monacoComponent $ MM.settings setup
