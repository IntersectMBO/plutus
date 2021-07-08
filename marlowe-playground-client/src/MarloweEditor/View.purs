module MarloweEditor.View where

import Prelude hiding (div)
import BottomPanel.Types (Action(..)) as BottomPanel
import BottomPanel.View (render) as BottomPanel
import Data.Array as Array
import Data.Bifunctor (bimap)
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (flex, flexCol, flexGrow, fullHeight, group, maxH70p, minH0, overflowHidden, paddingX)
import Halogen.Css (classNames)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, button, div, option, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled, id_, title)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Monaco as MM
import MarloweEditor.BottomPanel (panelContents)
import MarloweEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _editorErrors, _editorWarnings, _keybindings, contractHasErrors, contractHasHoles)
import Popper (Placement(..))
import Tooltip.State (tooltip)
import Tooltip.Types (ReferenceId(..))

render ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  ComponentHTML Action ChildSlots m
render metadata state =
  div [ classes [ flex, flexCol, fullHeight, paddingX ] ]
    [ section [ classes [ minH0, flexGrow, overflowHidden ] ]
        [ marloweEditor state ]
    , section [ classes [ maxH70p ] ]
        [ renderSubmodule
            _bottomPanelState
            BottomPanelAction
            (BottomPanel.render panelTitles wrapBottomPanelContents)
            state
        ]
    ]
  where
  panelTitles =
    [ { title: "Metadata", view: MetadataView, classes: [] }
    , { title: "Static Analysis", view: StaticAnalysisView, classes: [] }
    , { title: warningsTitle, view: MarloweWarningsView, classes: [] }
    , { title: errorsTitle, view: MarloweErrorsView, classes: [] }
    ]

  withCount str arry = str <> if Array.null arry then "" else " (" <> show (Array.length arry) <> ")"

  warningsTitle = withCount "Warnings" $ state ^. _editorWarnings

  errorsTitle = withCount "Errors" $ state ^. _editorErrors

  -- TODO: improve this wrapper helper
  actionWrapper = BottomPanel.PanelAction

  wrapBottomPanelContents panelView = bimap (map actionWrapper) actionWrapper $ panelContents state metadata panelView

otherActions :: forall m. MonadAff m => State -> ComponentHTML Action ChildSlots m
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , viewAsBlocklyButton state
    , sendToSimulatorButton state
    ]

sendToSimulatorButton ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
sendToSimulatorButton state =
  div [ id_ "marloweSendToSimulator" ]
    [ button
        [ onClick $ const $ Just SendToSimulator
        , disabled disabled'
        , classNames [ "btn" ]
        ]
        [ text "Send To Simulator" ]
    , tooltip tooltipMessage (RefId "marloweSendToSimulator") Bottom
    ]
  where
  disabled' = contractHasErrors state || contractHasHoles state

  tooltipMessage =
    if disabled' then
      "A contract can only be sent to the simulator if it has no errors and no holes"
    else
      "Execute this contract in the Marlowe simulator"

viewAsBlocklyButton :: forall p. State -> HTML p Action
viewAsBlocklyButton state =
  button
    ( [ onClick $ const $ Just ViewAsBlockly
      , disabled disabled'
      , classNames [ "btn" ]
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
  setup editor = pure unit

  component = monacoComponent $ MM.settings setup
