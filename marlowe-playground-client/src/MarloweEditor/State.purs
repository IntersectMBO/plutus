module MarloweEditor.State
  ( handleAction
  , editorGetValue
  , {- FIXME: this should be an action -} editorResize
  ) where

import Prelude hiding (div)
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (catMaybes)
import Data.Either (Either(..))
import Data.Lens (assign, set, use, view)
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, liftEffect, modify_, query)
import Halogen.Blockly as Blockly
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import MarloweEditor.Types (Action(..), State, _keybindings, _showBottomPanel)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _blocklySlot, _hasUnsavedChanges', _marloweEditorPageSlot)
import Marlowe (SPParams_, postRunghc)
import Monaco (IMarkerData, markerSeverity)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.Types (WebData, _result)
import StaticData (marloweBufferLocalStorageKey)
import Webghc.Server (CompileRequest(..))

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction _ (ChangeKeyBindings bindings) = do
  assign _keybindings bindings
  void $ query _marloweEditorPageSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  assign _hasUnsavedChanges' true

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

-- FIXME fix in the Mainframe (refactor from Simulation)
handleAction _ SetBlocklyCode = pure unit

handleAction _ (InitMarloweProject contents) = do
  editorSetValue contents
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey contents
  assign _hasUnsavedChanges' false

handleAction _ MarkProjectAsSaved = assign _hasUnsavedChanges' false

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorPageSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorPageSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorPageSlot unit (Monaco.GetText identity)
