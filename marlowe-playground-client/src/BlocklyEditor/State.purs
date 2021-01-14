module BlocklyEditor.State where

import Prelude
import BlocklyEditor.Types (Action(..), State, _errorMessage, _marloweCode)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Data.Bifunctor (lmap)
import Data.Either (note, Either(..))
import Data.Lens (assign)
import Data.Maybe (Maybe(..))
import Debug.Trace (spy)
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, query)
import Halogen as H
import Halogen.Blockly as Blockly
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Parser as Parser
import Text.Extra as Text
import Text.Pretty (pretty)

handleAction ::
  forall m.
  MonadAff m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction (HandleBlocklyMessage Blockly.CodeChange) = do
  eContract <-
    runExceptT do
      code <- ExceptT <<< map (note "Blockly Workspace is empty") $ query _blocklySlot unit $ H.request Blockly.GetCode
      except <<< lmap (unexpected <<< show) $ Parser.parseContract (Text.stripParens code)
  case eContract of
    Left e -> do
      assign _errorMessage $ Just e
      assign _marloweCode Nothing
    Right contract -> do
      assign _errorMessage Nothing
      assign _marloweCode $ Just $ show $ pretty contract
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleAction (InitBlocklyProject code) = do
  assign _marloweCode $ Just code
  void $ query _blocklySlot unit $ H.tell (Blockly.SetCode code)

handleAction SendToSimulator = pure unit

handleAction ViewAsMarlowe = pure unit

handleAction Save = pure unit

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _blocklySlot unit $ H.request Blockly.GetCode
