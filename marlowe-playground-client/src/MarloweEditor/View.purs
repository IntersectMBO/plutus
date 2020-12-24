module MarloweEditor.View where

import Prelude hiding (div)
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens ((^.))
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (codeEditor, group)
import Halogen.HTML (HTML, button, div, div_, option, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (class_, classes, disabled)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Marlowe.Monaco as MM
import MarloweEditor.BottomPanel (bottomPanel)
import MarloweEditor.Types (Action(..), State, _keybindings, _showBottomPanel)
import Monaco (getModel, setValue) as Monaco
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ marloweEditor state ]
        ]
    , bottomPanel state
    ]

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editorOptions state
    , sendToButton state "Send To Simulator" SendToSimulator
    -- , sendToButton state "Send To Blockly" SendResultToBlockly
    ]

sendToButton :: forall p. State -> String -> Action -> HTML p Action
sendToButton state msg action =
  -- FIXME: Only make available when there are no compilation errors
  -- FIXME: instead of not showing, add a disable flag and maybe a tooltip
  if true then
    button
      [ onClick $ const $ Just action
      , disabled (false)
      ]
      [ text msg ]
  else
    text ""

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
