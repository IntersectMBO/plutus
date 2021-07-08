-- TODO: rename modules from BlocklyEditor -> MarloweBlocklyEditor
module BlocklyEditor.State where

import Prelude
import BlocklyComponent.Types as Blockly
import BlocklyEditor.Types (Action(..), BottomPanelView, State, _bottomPanelState, _errorMessage, _hasHoles, _marloweCode, _metadataHintInfo, _warnings)
import BottomPanel.State (handleAction) as BottomPanel
import BottomPanel.Types (Action(..), State) as BottomPanel
import CloseAnalysis (analyseClose)
import Control.Monad.Except (ExceptT(..), except, lift, runExceptT)
import Control.Monad.Maybe.Extra (hoistMaybe)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Reader (class MonadAsk)
import Data.Array as Array
import Data.Either (Either(..), hush, note)
import Data.Lens (assign, modifying, over, set, use, view)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Env (Env)
import Examples.Marlowe.Contracts (example) as ME
import Halogen (HalogenM, modify_, query)
import Halogen as H
import Halogen.Extra (mapSubmodule)
import MainFrame.Types (ChildSlots, _blocklySlot)
import Marlowe.Blockly as MB
import Marlowe.Extended as Extended
import Marlowe.Holes as Holes
import Marlowe.Linter as Linter
import Marlowe.Template (TemplateContent)
import Marlowe.Template as Template
import SessionStorage as SessionStorage
import Simulator.Lenses (_templateContent)
import StaticAnalysis.Reachability (analyseReachability, getUnreachableContracts)
import StaticAnalysis.StaticTools (analyseContract)
import StaticAnalysis.Types (AnalysisExecutionState(..), _analysisExecutionState, _analysisState)
import StaticData (marloweBufferLocalStorageKey)
import Text.Pretty (pretty)

toBottomPanel ::
  forall m a.
  Functor m =>
  HalogenM (BottomPanel.State BottomPanelView) (BottomPanel.Action BottomPanelView Action) ChildSlots Void m a ->
  HalogenM State Action ChildSlots Void m a
toBottomPanel = mapSubmodule _bottomPanelState BottomPanelAction

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction (HandleBlocklyMessage Blockly.BlocklyReady) = do
  mContents <- liftEffect $ SessionStorage.getItem marloweBufferLocalStorageKey
  handleAction $ InitBlocklyProject $ fromMaybe ME.example mContents

handleAction (HandleBlocklyMessage Blockly.CodeChange) = processBlocklyCode

handleAction (HandleBlocklyMessage (Blockly.BlockSelection selection)) = case mBlockDefinition of
  Nothing -> void $ query _blocklySlot unit $ H.tell (Blockly.SetToolbox MB.toolbox)
  Just definition -> void $ query _blocklySlot unit $ H.tell (Blockly.SetToolbox $ MB.toolboxWithHoles definition)
  where
  mBlockDefinition = do
    { blockType } <- selection
    Map.lookup blockType MB.definitionsMap

handleAction (InitBlocklyProject code) = do
  void $ query _blocklySlot unit $ H.tell $ Blockly.SetCode code
  processBlocklyCode
  -- Reset the toolbox
  void $ query _blocklySlot unit $ H.tell (Blockly.SetToolbox MB.toolbox)

handleAction SendToSimulator = pure unit

handleAction ViewAsMarlowe = pure unit

handleAction Save = pure unit

handleAction (BottomPanelAction (BottomPanel.PanelAction action)) = handleAction action

handleAction (BottomPanelAction action) = toBottomPanel (BottomPanel.handleAction action)

handleAction (SetIntegerTemplateParam templateType key value) =
  modifying
    (_analysisState <<< _templateContent <<< Template.typeToLens templateType)
    (Map.insert key value)

handleAction (MetadataAction _) = pure unit

handleAction AnalyseContract = runAnalysis $ analyseContract

handleAction AnalyseReachabilityContract = runAnalysis $ analyseReachability

handleAction AnalyseContractForCloseRefund = runAnalysis $ analyseClose

handleAction ClearAnalysisResults = assign (_analysisState <<< _analysisExecutionState) NoneAsked

handleAction (SelectWarning warning) = void $ query _blocklySlot unit $ H.tell (Blockly.SelectWarning warning)

-- This function reads the Marlowe code from blockly and, process it and updates the component state
processBlocklyCode ::
  forall m.
  MonadAff m =>
  HalogenM State Action ChildSlots Void m Unit
processBlocklyCode = do
  eContract <-
    runExceptT do
      block <- ExceptT <<< map (note "Blockly Workspace is empty") $ query _blocklySlot unit $ H.request Blockly.GetBlockRepresentation
      except $ MB.blockToContract block
  case eContract of
    Left e ->
      modify_
        ( set _errorMessage (Just $ unexpected e)
            <<< set _marloweCode Nothing
        )
    Right holesContract -> do
      analysisExecutionState <- use (_analysisState <<< _analysisExecutionState)
      let
        unreachableContracts = getUnreachableContracts analysisExecutionState

        lintingState = Linter.lint unreachableContracts holesContract

        prettyContract = show $ pretty holesContract

        -- If we can get an Extended contract from the holes contract (basically if it has no holes)
        -- then update the template content. If not, leave them as they are
        maybeUpdateTemplateContent :: TemplateContent -> TemplateContent
        maybeUpdateTemplateContent = case Holes.fromTerm holesContract of
          Just (contract :: Extended.Contract) -> Template.updateTemplateContent $ Template.getPlaceholderIds contract
          Nothing -> identity
      liftEffect $ SessionStorage.setItem marloweBufferLocalStorageKey prettyContract
      modify_
        ( set _errorMessage Nothing
            <<< set _marloweCode (Just $ prettyContract)
            <<< set _hasHoles (Linter.hasHoles $ lintingState)
            <<< set _warnings (Array.fromFoldable $ view Linter._warnings lintingState)
            <<< set _metadataHintInfo (view Linter._metadataHints lintingState)
            <<< over (_analysisState <<< _templateContent) maybeUpdateTemplateContent
        )
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

runAnalysis ::
  forall m.
  MonadAff m =>
  (Extended.Contract -> HalogenM State Action ChildSlots Void m Unit) ->
  HalogenM State Action ChildSlots Void m Unit
runAnalysis doAnalyze =
  void
    $ runMaybeT do
        block <- MaybeT $ query _blocklySlot unit $ H.request Blockly.GetBlockRepresentation
        -- FIXME: See if we can use runExceptT and show the error somewhere
        contract <- MaybeT $ pure $ Holes.fromTerm =<< (hush $ MB.blockToContract block)
        lift do
          doAnalyze contract
          processBlocklyCode

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue =
  runMaybeT do
    block <- MaybeT $ query _blocklySlot unit $ H.request Blockly.GetBlockRepresentation
    contract <- hoistMaybe $ hush $ MB.blockToContract block
    pure $ show $ pretty $ contract
