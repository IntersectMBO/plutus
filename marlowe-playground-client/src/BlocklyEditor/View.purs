module BlocklyEditor.View where

import Prelude hiding (div)
import Blockly.Internal (block, blockType, category, colour, name, style, x, xml, y)
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

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ flex, flexCol, fullHeight ] ]
    [ section
        [ classes [ paddingX, minH0, overflowHidden, fullHeight ]
        ]
        [ slot _blocklySlot unit (Blockly.blocklyComponent MB.rootBlockName MB.blockDefinitions) unit (Just <<< HandleBlocklyMessage)
        , toolbox
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

  wrapBottomPanelContents panelView = BottomPanel.PanelAction <$> panelContents state panelView

toolbox :: forall a b. HTML a b
toolbox =
  xml [ id_ "blocklyToolbox", style "display:none" ]
    [ category [ name "Contracts", colour MB.contractColour ] (map mkBlock MB.contractTypes)
    , category [ name "Observations", colour MB.observationColour ] (map mkBlock MB.observationTypes)
    , category [ name "Actions", colour MB.actionColour ] (map mkBlock MB.actionTypes)
    , category [ name "Values", colour MB.valueColour ] (map mkBlock MB.valueTypes)
    , category [ name "Payee", colour MB.payeeColour ] (map mkBlock MB.payeeTypes)
    , category [ name "Party", colour MB.partyColour ] (map mkBlock MB.partyTypes)
    , category [ name "Token", colour MB.tokenColour ] (map mkBlock MB.tokenTypes)
    , category [ name "Bounds", colour MB.boundsColour ] (map mkBlock [ MB.BoundsType ])
    ]
  where
  mkBlock :: forall t. Show t => t -> _
  mkBlock t = block [ blockType (show t) ] []

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
