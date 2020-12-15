module MarloweEditor.View where

import Prelude hiding (div)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.Lens (has, to, view, (^.))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Examples.Haskell.Contracts as HE
import Halogen (ClassName(..), ComponentHTML, liftEffect)
import Halogen.Classes (aHorizontal, analysisPanel, closeDrawerArrowIcon, codeEditor, collapsed, footerPanelBg, group, minimizeIcon)
import Halogen.HTML (HTML, a, button, code_, div, div_, img, option, pre_, section, select, slot, text)
import Halogen.HTML.Events (onClick, onSelectedIndexChange)
import Halogen.HTML.Properties (alt, class_, classes, disabled, src)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import MarloweEditor.Types (Action(..), State, _keybindings, _showBottomPanel)
import Marlowe.Monaco as MM
import Language.Haskell.Interpreter (CompilationError(..), InterpreterError(..), InterpreterResult(..))
import Language.Haskell.Monaco as HM
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _marloweEditorPageSlot)
import Monaco (getModel, setValue) as Monaco
import Network.RemoteData (RemoteData(..), _Loading, isLoading, isSuccess)
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
    -- , sendResultButton state "Send To Simulator" SendResultToSimulator
    -- , sendResultButton state "Send To Blockly" SendResultToBlockly
    ]

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

bottomPanel :: forall p. State -> HTML p Action
bottomPanel state = div_ [ text "" ]
