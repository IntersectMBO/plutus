module BlocklyComponent.State where

import Prelude hiding (div)
import Blockly.Generator (blockToCode, newBlock)
import Blockly.Internal (BlockDefinition, ElementId(..), getBlockById)
import Blockly.Internal as Blockly
import BlocklyComponent.Types (Action(..), Message(..), Query(..), State, _blocklyState, _errorMessage, _generator, _useEvents, emptyState)
import BlocklyComponent.View (render)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.Traversable (for, for_)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (Component, HalogenM, liftEffect, mkComponent, modify_)
import Halogen as H
import Halogen.BlocklyCommons (updateUnsavedChangesActionHandler, blocklyEvents)
import Halogen.HTML (HTML)
import Marlowe.Blockly (buildBlocks, buildGenerator)
import Marlowe.Holes (Term(..))
import Marlowe.Parser as Parser
import Prim.TypeError (class Warn, Text)
import Text.Extra as Text
import Type.Proxy (Proxy(..))

blockly ::
  forall m.
  MonadAff m =>
  String ->
  Array BlockDefinition ->
  Component HTML Query Unit Message m
blockly rootBlockName blockDefinitions =
  mkComponent
    { initialState: const emptyState
    , render
    , eval:
        H.mkEval
          { handleQuery
          , handleAction
          , initialize: Just $ Inject rootBlockName blockDefinitions
          , finalize: Nothing
          , receive: Just <<< SetData
          }
    }

handleQuery ::
  forall slots m a.
  MonadEffect m =>
  Query a ->
  HalogenM State Action slots Message m (Maybe a)
handleQuery (Resize next) = do
  mState <- use _blocklyState
  case mState of
    Just state ->
      pure
        $ ST.run do
            workspaceRef <- STRef.new state.workspace
            Blockly.resize state.blockly workspaceRef
    Nothing -> pure unit
  pure $ Just next

handleQuery (SetCode code next) = do
  mState <- use _blocklyState
  case mState of
    Nothing -> pure unit
    Just blocklyState -> do
      assign _useEvents false
      let
        contract = case Parser.parseContract (Text.stripParens code) of
          Right c -> c
          Left _ -> Hole blocklyState.rootBlockName Proxy zero
      pure $ ST.run (buildBlocks newBlock blocklyState contract)
  assign _errorMessage Nothing
  pure $ Just next

handleQuery (SetError err next) = do
  assign _errorMessage $ Just err
  pure $ Just next

handleQuery (GetWorkspace f) = do
  mState <- use _blocklyState
  for mState \bs -> do
    let
      xml = Blockly.workspaceXML bs.blockly bs.workspace
    pure $ f xml

handleQuery (LoadWorkspace xml next) = do
  mState <- use _blocklyState
  for_ mState \state ->
    pure
      $ ST.run do
          workspaceRef <- STRef.new state.workspace
          Blockly.loadWorkspace state.blockly workspaceRef xml
  assign _errorMessage Nothing
  pure $ Just next

handleQuery (GetCode next) = do
  eCode <-
    runExceptT do
      blocklyState <- ExceptT <<< map (note $ unexpected "BlocklyState not set") $ use _blocklyState
      generator <- ExceptT <<< map (note $ unexpected "Generator not set") $ use _generator
      let
        workspace = blocklyState.workspace

        rootBlockName = blocklyState.rootBlockName
      block <- except <<< (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
      except <<< lmap unexpected $ blockToCode block generator
  case eCode of
    Left e -> do
      assign _errorMessage $ Just e
      pure Nothing
    Right code -> do
      assign _errorMessage Nothing
      pure <<< Just <<< next $ code
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleAction ::
  forall m slots.
  Warn (Text "SCP-1648 Fix blockly code being lost after refresh") =>
  MonadAff m =>
  Action ->
  HalogenM State Action slots Message m Unit
handleAction (Inject rootBlockName blockDefinitions) = do
  blocklyState <- liftEffect $ Blockly.createBlocklyInstance rootBlockName (ElementId "blocklyWorkspace") (ElementId "blocklyToolbox")
  let
    _ =
      -- NOTE: This could be refactored to use Effect instead of ST
      -- https://github.com/input-output-hk/plutus/pull/2498#discussion_r533371159
      ST.run
        ( do
            blocklyRef <- STRef.new blocklyState.blockly
            workspaceRef <- STRef.new blocklyState.workspace
            Blockly.addBlockTypes blocklyRef blockDefinitions
            Blockly.initializeWorkspace blocklyState.blockly workspaceRef
        )

    generator = buildGenerator blocklyState
  void $ H.subscribe $ blocklyEvents BlocklyEvent blocklyState.workspace
  modify_
    ( set _blocklyState (Just blocklyState)
        <<< set _generator (Just generator)
    )

handleAction (SetData _) = pure unit

handleAction (BlocklyEvent event) = updateUnsavedChangesActionHandler CodeChange event
