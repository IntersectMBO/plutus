-- TODO: rename modules from BlocklyEditor -> MarloweBlocklyEditor
module BlocklyEditor.State where

import Prelude
import BlocklyComponent.Types as Blockly
import BlocklyEditor.Types (Action(..), State, _errorMessage, _hasHoles, _marloweCode)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either, hush, note)
import Data.Lens (set)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM, modify_, query)
import Halogen as H
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Blockly (blockToContract)
import Marlowe.Linter as Linter
import Marlowe.Parser as Parser
import Text.Pretty (pretty)

handleAction ::
  forall m.
  MonadAff m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction (HandleBlocklyMessage Blockly.CodeChange) = do
  eContract <-
    runExceptT do
      block <- ExceptT <<< map (note "Blockly Workspace is empty") $ query _blocklySlot unit $ H.request Blockly.GetBlockRepresentation
      except $ blockToContract block
  case eContract of
    Left e ->
      modify_
        ( set _errorMessage (Just $ unexpected e)
            <<< set _marloweCode Nothing
        )
    Right contract ->
      let
        hasHoles = Linter.hasHoles $ Linter.lint Nil contract
      in
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
editorGetValue =
  runMaybeT do
    block <- MaybeT $ query _blocklySlot unit $ H.request Blockly.GetBlockRepresentation
    contract <- hoistMaybe $ hush $ blockToContract block
    pure $ show $ pretty $ contract
