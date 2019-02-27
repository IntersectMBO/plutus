module Types where

import Prelude

import Ace.Halogen.Component (AceMessage, AceQuery)
import Auth (AuthStatus)
import Control.Comonad (class Comonad, extract)
import Control.Extend (class Extend, extend)
import DOM.HTML.Event.Types (DragEvent)
import Data.Array as Array
import Data.Either (Either)
import Data.Generic (class Generic, gShow)
import Data.Lens (Lens', Prism', Lens, _2, over, prism', traversed, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Gist (Gist)
import Halogen.Component.ChildPath (ChildPath, cpI)
import Language.Haskell.Interpreter (CompilationError)
import Network.RemoteData (RemoteData)
import API (RunResult)
import Servant.PureScript.Affjax (AjaxError)

------------------------------------------------------------

data Query a
  -- SubEvents.
  = HandleEditorMessage AceMessage a
  | HandleDragEvent DragEvent a
  | HandleDropEvent DragEvent a
  -- Gist support.
  | CheckAuthStatus a
  | PublishGist a
  -- Tabs.
  | ChangeView View a
  -- Editor.
  | LoadScript String a
  | CompileProgram a
  | ScrollTo { row :: Int, column :: Int } a

------------------------------------------------------------

type ChildQuery = AceQuery
type ChildSlot = EditorSlot

data EditorSlot = EditorSlot
derive instance eqComponentEditorSlot :: Eq EditorSlot
derive instance ordComponentEditorSlot :: Ord EditorSlot

cpEditor :: ChildPath AceQuery ChildQuery EditorSlot ChildSlot
cpEditor = cpI

-----------------------------------------------------------

type State =
  { view :: View
  , runResult :: RemoteData AjaxError (Either (Array CompilationError) RunResult)
  , authStatus :: RemoteData AjaxError AuthStatus
  , createGistResult :: RemoteData AjaxError Gist
  }

_view :: forall s a. Lens' {view :: a | s} a
_view = prop (SProxy :: SProxy "view")

_runResult :: forall s a. Lens' {runResult :: a | s} a
_runResult = prop (SProxy :: SProxy "runResult")

_authStatus :: forall s a. Lens' {authStatus :: a | s} a
_authStatus = prop (SProxy :: SProxy "authStatus")

_createGistResult :: forall s a. Lens' {createGistResult :: a | s} a
_createGistResult = prop (SProxy :: SProxy "createGistResult")

data View
  = Editor

derive instance eqView :: Eq View
derive instance genericView :: Generic View

instance showView :: Show View where
  show = gShow