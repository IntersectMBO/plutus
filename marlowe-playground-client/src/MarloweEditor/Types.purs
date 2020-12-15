module MarloweEditor.Types where

import Prelude
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Either (Either(..))
import Data.Lens (Getter', Lens', Fold', _Right, to)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Halogen.Monaco (KeyBindings(..))
import Halogen.Monaco as Monaco
import Language.Haskell.Interpreter (InterpreterError, InterpreterResult, _InterpreterResult)
import Marlowe.Parser (parseContract)
import Network.RemoteData (RemoteData(..), _Success)
import Simulation.Types (AnalysisState(..), WebData)
import Text.Pretty (pretty)

data Action
  = ChangeKeyBindings KeyBindings
  | HandleEditorMessage Monaco.Message
  | ShowBottomPanel Boolean
  | SetBlocklyCode
  | InitMarloweProject String
  | MarkProjectAsSaved

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "MarloweEditor." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent (ChangeKeyBindings _) = Just $ defaultEvent "ChangeKeyBindings"
  toEvent (HandleEditorMessage _) = Just $ defaultEvent "HandleEditorMessage"
  toEvent (ShowBottomPanel _) = Just $ defaultEvent "ShowBottomPanel"
  toEvent SetBlocklyCode = Just $ defaultEvent "SetBlocklyCode"
  toEvent (InitMarloweProject _) = Just $ defaultEvent "InitMarloweProject"
  toEvent MarkProjectAsSaved = Just $ defaultEvent "MarkProjectAsSaved"

type State
  = { keybindings :: KeyBindings
    , showBottomPanel :: Boolean
    , hasUnsavedChanges :: Boolean
    , selectedHole :: Maybe String
    -- This is pagination information that we need to provide to the haskell backend
    -- so that it can do the analysis in chunks
    , analysisState :: AnalysisState
    }

_keybindings :: Lens' State KeyBindings
_keybindings = prop (SProxy :: SProxy "keybindings")

_showBottomPanel :: Lens' State Boolean
_showBottomPanel = prop (SProxy :: SProxy "showBottomPanel")

_selectedHole :: Lens' State (Maybe String)
_selectedHole = prop (SProxy :: SProxy "selectedHole")

_analysisState :: Lens' State AnalysisState
_analysisState = prop (SProxy :: SProxy "analysisState")

initialState :: State
initialState =
  { keybindings: DefaultBindings
  , showBottomPanel: true
  , hasUnsavedChanges: false
  , selectedHole: Nothing
  , analysisState: NoneAsked
  }
