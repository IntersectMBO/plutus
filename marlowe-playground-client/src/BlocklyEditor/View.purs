module BlocklyEditor.View where

import Prelude hiding (div)
import BlocklyEditor.Types (Action(..), State, _marloweCode)
import Data.Lens ((^.))
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Blockly as Blockly
import Halogen.Classes (disabled, group)
import Halogen.HTML (HTML, button, div, slot, text, div_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, enabled)
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Blockly as MB

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ slot _blocklySlot unit (Blockly.blockly MB.rootBlockName MB.blockDefinitions) unit (Just <<< HandleBlocklyMessage)
    , MB.toolbox
    , MB.workspaceBlocks
    ]

otherActions ::
  forall p.
  State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ button
        [ onClick $ const $ Just ViewAsMarlowe
        , enabled hasCode
        , classes [ disabled hasCode ]
        ]
        [ text "View as Marlowe" ]
    , button
        [ onClick $ const $ Just SendToSimulator
        , enabled hasCode
        , classes [ disabled hasCode ]
        ]
        [ text "Send To Simulator" ]
    ]
  where
  hasCode = isJust $ state ^. _marloweCode
