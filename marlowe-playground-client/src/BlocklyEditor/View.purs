module BlocklyEditor.View where

import Prelude hiding (div)
import Blockly.Internal (block, blockType, style, x, xml, y)
import BlocklyComponent.State as Blockly
import BlocklyEditor.BottomPanel (panelContents)
import BlocklyEditor.Types (Action(..), BottomPanelView(..), State, _bottomPanelState, _hasHoles, _marloweCode, _warnings)
import BottomPanel.Types (Action(..)) as BottomPanel
import BottomPanel.View (render) as BottomPanel
import Data.Array as Array
import Data.Lens ((^.))
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Classes (flex, flexCol, fullHeight, group, maxH70p, minH0, overflowHidden, paddingX)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (HTML, button, div, section, slot, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, enabled, id_)
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Blockly as MB
import Marlowe.Extended.Metadata (MetaData)

render ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  ComponentHTML Action ChildSlots m
render metadata state =
  div [ classes [ flex, flexCol, fullHeight ] ]
    [ section
        [ classes [ paddingX, minH0, overflowHidden, fullHeight ]
        ]
        [ slot _blocklySlot unit (Blockly.blocklyComponent MB.rootBlockName MB.blockDefinitions MB.toolbox) unit (Just <<< HandleBlocklyMessage)
        , workspaceBlocks
        ]
    , section [ classes [ paddingX, maxH70p ] ]
        [ renderSubmodule
            _bottomPanelState
            BottomPanelAction
            (BottomPanel.render panelTitles wrapBottomPanelContents)
            state
        ]
    ]
  where
  panelTitles =
    [ { title: "Static Analysis", view: StaticAnalysisView, classes: [] }
    , { title: warningsTitle, view: BlocklyWarningsView, classes: [] }
    ]

  withCount str arry = str <> if Array.null arry then "" else " (" <> show (Array.length arry) <> ")"

  warningsTitle = withCount "Warnings" $ state ^. _warnings

  wrapBottomPanelContents panelView = BottomPanel.PanelAction <$> panelContents state metadata panelView

workspaceBlocks :: forall a b. HTML a b
workspaceBlocks =
  xml [ id_ "workspaceBlocks", style "display:none" ]
    [ block [ blockType (show MB.BaseContractType), x "13", y "187", id_ MB.rootBlockName ] []
    ]

otherActions ::
  forall p.
  State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ button
        [ onClick $ const $ Just ViewAsMarlowe
        , enabled hasCode
        ]
        [ text "View as Marlowe" ]
    , button
        [ onClick $ const $ Just SendToSimulator
        , enabled (hasCode && not hasHoles)
        ]
        [ text "Send To Simulator" ]
    ]
  where
  hasCode = isJust $ state ^. _marloweCode

  hasHoles = state ^. _hasHoles
