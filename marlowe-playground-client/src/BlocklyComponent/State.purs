module BlocklyComponent.State where

import Prelude hiding (div)
import Blockly.Dom (explainError, getDom)
import Blockly.Generator (newBlock)
import Blockly.Internal (BlockDefinition, ElementId(..))
import Blockly.Internal as Blockly
import BlocklyComponent.Types (Action(..), Message(..), Query(..), State, _blocklyEventSubscription, _blocklyState, _errorMessage, _generator, emptyState)
import BlocklyComponent.View (render)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), either, note)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Data.Traversable (for, for_)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (Component, HalogenM, liftEffect, mkComponent, modify_)
import Halogen as H
import Halogen.BlocklyCommons (blocklyEvents, runWithoutEventSubscription, detectCodeChanges)
import Halogen.HTML (HTML)
import Marlowe.Blockly (blockToContract, buildBlocks, buildGenerator)
import Marlowe.Holes (Term(..), Location(..))
import Marlowe.Parser as Parser
import Prim.TypeError (class Warn, Text)
import Text.Extra as Text
import Text.Pretty (pretty)
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
  MonadAff m =>
  Query a ->
  HalogenM State Action slots Message m (Maybe a)
handleQuery (Resize next) = do
  mState <- use _blocklyState
  for_ mState \{ blockly, workspace } ->
    liftEffect $ Blockly.resize blockly workspace
  pure $ Just next

handleQuery (SetCode code next) = do
  mState <- use _blocklyState
  for_ mState \blocklyState -> do
    let
      contract =
        either
          (const $ Hole blocklyState.rootBlockName Proxy NoLocation)
          identity
          $ Parser.parseContract (Text.stripParens code)
    -- Create the blocks temporarily disabling the blockly events until they settle
    -- FIXME: check why buildBlocks requires we pass newBlock
    runWithoutEventSubscription 100 BlocklyEvent $ buildBlocks newBlock blocklyState contract
  assign _errorMessage Nothing
  pure $ Just next

handleQuery (SetError err next) = do
  assign _errorMessage $ Just err
  pure $ Just next

handleQuery (GetWorkspace f) = do
  mState <- use _blocklyState
  for mState \bs -> do
    xml <- liftEffect $ Blockly.workspaceXML bs.blockly bs.workspace
    pure $ f xml

handleQuery (LoadWorkspace xml next) = do
  mState <- use _blocklyState
  for_ mState \{ blockly, workspace } ->
    liftEffect $ Blockly.loadWorkspace blockly workspace xml
  assign _errorMessage Nothing
  pure $ Just next

handleQuery (GetCode next) = do
  mBlocklyState <- use _blocklyState
  mGenerator <- use _generator
  eCode <-
    liftEffect
      $ runExceptT do
          { blockly, workspace, rootBlockName } <- except <<< (note $ unexpected "BlocklyState not set") $ mBlocklyState
          -- FIXME: Eventually BlocklyComponent should return the Block representation defined in Blockly.Dom and it should be
          --        the parents responsability to transform it to code. That way we dont need to specify which `blockToTerm` to use
          --        and allow to share this component between Marlowe and Actus Blockly
          block <- ExceptT $ lmap explainError <$> getDom blockly workspace rootBlockName
          ExceptT $ pure $ show <<< pretty <$> blockToContract block
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
  blocklyState /\ generator <-
    liftEffect do
      state <- Blockly.createBlocklyInstance rootBlockName (ElementId "blocklyWorkspace") (ElementId "blocklyToolbox")
      Blockly.addBlockTypes state.blockly blockDefinitions
      Blockly.initializeWorkspace state.blockly state.workspace
      generator <- buildGenerator state.blockly
      pure $ Tuple state generator
  eventSubscription <- H.subscribe $ blocklyEvents BlocklyEvent blocklyState.workspace
  modify_
    ( set _blocklyState (Just blocklyState)
        <<< set _generator (Just generator)
        <<< set _blocklyEventSubscription (Just eventSubscription)
    )

handleAction (SetData _) = pure unit

handleAction (BlocklyEvent event) = detectCodeChanges CodeChange event
