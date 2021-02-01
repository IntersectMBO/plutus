module BlocklyEditor.State where

import Prelude
import BlocklyEditor.Types (Action(..), State, _errorMessage, _hasHoles, _marloweCode)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either, note)
import Data.Lens (set)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, modify_, query)
import Halogen as H
import BlocklyComponent.Types as Blockly
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Linter as Linter
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
      contract <- except <<< lmap (unexpected <<< show) $ Parser.parseContract (Text.stripParens code)
      let
        hasHoles = Linter.hasHoles $ Linter.lint Nil contract
      pure $ Tuple contract hasHoles
  case eContract of
    Left e ->
      modify_
        ( set _errorMessage (Just e)
            <<< set _marloweCode Nothing
        )
    Right (contract /\ hasHoles) ->
      modify_
        ( set _errorMessage Nothing
            <<< set _marloweCode (Just $ show $ pretty contract)
            <<< set _hasHoles hasHoles
        )
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleAction (InitBlocklyProject code) = do
  void $ query _blocklySlot unit $ H.tell (Blockly.SetCode code)
  let
    hasHoles = either (const false) identity $ (Linter.hasHoles <<< Linter.lint Nil) <$> Parser.parseContract code
  modify_
    ( set _marloweCode (Just code)
        <<< set _hasHoles hasHoles
    )

handleAction SendToSimulator = pure unit

handleAction ViewAsMarlowe = pure unit

handleAction Save = pure unit

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _blocklySlot unit $ H.request Blockly.GetCode
