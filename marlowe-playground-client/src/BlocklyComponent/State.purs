module BlocklyComponent.State (blocklyComponent) where

import Prelude hiding (div)
import Blockly.Dom (explainError, getDom)
import Blockly.Events (newElementId)
import Blockly.Generator (newBlock)
import Blockly.Internal (BlockDefinition, ElementId(..), centerOnBlock, getBlockById, getBlockType, select, updateToolbox)
import Blockly.Internal as Blockly
import Blockly.Toolbox (Toolbox)
import Blockly.Types as BT
import BlocklyComponent.Types (Action(..), Message(..), Query(..), State, _blocklyEventSubscription, _blocklyState, _errorMessage, blocklyRef, emptyState)
import BlocklyComponent.View (render)
import Control.Monad.Except (ExceptT(..), runExceptT, withExceptT)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Either (Either(..), either, note)
import Data.Lens (assign, set, use, view)
import Data.Maybe (Maybe(..))
import Data.Traversable (for, for_)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception.Unsafe (unsafeThrow)
import Halogen (Component, HalogenM, getHTMLElementRef, liftEffect, mkComponent, modify_, raise)
import Halogen as H
import Halogen.BlocklyCommons (blocklyEvents, runWithoutEventSubscription, detectCodeChanges)
import Halogen.ElementResize (elementResize)
import Halogen.ElementVisible (elementVisible)
import Halogen.HTML (HTML)
import Marlowe.Blockly (buildBlocks)
import Marlowe.Holes (Term(..), Location(..))
import Marlowe.Linter (_location)
import Marlowe.Parser as Parser
import Text.Extra as Text
import Type.Proxy (Proxy(..))
import Web.DOM.ResizeObserver (ResizeObserverBoxOptions(..))
import Web.HTML.HTMLElement as HTMLElement

blocklyComponent ::
  forall m.
  MonadAff m =>
  String ->
  Array BlockDefinition ->
  Toolbox ->
  Component HTML Query Unit Message m
blocklyComponent rootBlockName blockDefinitions toolbox =
  mkComponent
    { initialState: const emptyState
    , render
    , eval:
        H.mkEval
          { handleQuery
          , handleAction
          , initialize: Just $ Inject rootBlockName blockDefinitions toolbox
          , finalize: Nothing
          , receive: Just <<< SetData
          }
    }

handleQuery ::
  forall slots m a.
  MonadAff m =>
  Query a ->
  HalogenM State Action slots Message m (Maybe a)
handleQuery (SetCode clearUndoStack code next) = do
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
    runWithoutEventSubscription 100 BlocklyEvent $ buildBlocks clearUndoStack newBlock blocklyState contract
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

handleQuery (GetBlockRepresentation next) = do
  eBlock <-
    runExceptT do
      blocklyState <- ExceptT $ note "BlocklyState not set" <$> use _blocklyState
      withExceptT explainError (getDom blocklyState)
  case eBlock of
    Left e -> do
      assign _errorMessage $ Just $ unexpected e
      pure Nothing
    Right block -> do
      assign _errorMessage Nothing
      pure <<< Just <<< next $ block
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleQuery (SelectWarning warning next) = do
  let
    blockId = locationToBlockId $ view _location warning
  void
    $ runMaybeT do
        blocklyState <- MaybeT $ use _blocklyState
        block <- MaybeT $ liftEffect $ getBlockById blocklyState.workspace blockId
        MaybeT $ map pure
          $ liftEffect do
              select block
              centerOnBlock blocklyState.workspace blockId
  pure $ Just next

handleQuery (SetToolbox toolbox next) = do
  void
    $ runMaybeT do
        blocklyState <- MaybeT $ use _blocklyState
        MaybeT $ map pure $ liftEffect $ updateToolbox toolbox blocklyState.workspace
  pure $ Just next

-- We cannot guarantee at the type level that the only type of location we handle in this editor
-- is a BlockId location, so we throw a useful error if we ever get to this situation
locationToBlockId :: Location -> String
locationToBlockId (BlockId blockId) = blockId

locationToBlockId (Range _) = unsafeThrow "Unexpected Range location found in MarloweParser"

locationToBlockId NoLocation = unsafeThrow "Unexpected NoLocation found in MarloweParser"

handleAction ::
  forall m slots.
  MonadAff m =>
  Action ->
  HalogenM State Action slots Message m Unit
handleAction (Inject rootBlockName blockDefinitions toolbox) = do
  mElement <- (pure <<< map HTMLElement.toElement) =<< getHTMLElementRef blocklyRef
  blocklyState <-
    liftEffect do
      -- TODO: once we refactor ActusBlockly to use BlocklyComponent we should remove ElementId from
      --       createBlocklyInstance and receive two HTMLElements that should be handled by RefElement
      state <- Blockly.createBlocklyInstance rootBlockName (ElementId "blocklyWorkspace") toolbox
      Blockly.addBlockTypes state.blockly blockDefinitions
      Blockly.initializeWorkspace state.blockly state.workspace
      pure state
  -- Subscribe to the resize events on the main section to resize blockly automatically.
  for_ mElement $ H.subscribe <<< elementResize ContentBox (const ResizeWorkspace)
  -- Subscribe to events triggered when blockly becames visible or hidden.
  for_ mElement $ H.subscribe <<< elementVisible VisibilityChanged
  -- Subscribe to blockly events to see when the code has changed.
  eventSubscription <- H.subscribe $ blocklyEvents BlocklyEvent blocklyState.workspace
  modify_
    ( set _blocklyState (Just blocklyState)
        <<< set _blocklyEventSubscription (Just eventSubscription)
    )

handleAction (SetData _) = pure unit

handleAction (BlocklyEvent (BT.Select event)) = case newElementId event of
  Nothing -> raise $ BlockSelection Nothing
  Just blockId -> do
    void
      $ runMaybeT do
          blocklyState <- MaybeT $ use _blocklyState
          block <- MaybeT $ liftEffect $ getBlockById blocklyState.workspace blockId
          blockType <- MaybeT $ map pure $ liftEffect $ getBlockType block
          MaybeT $ map pure $ raise $ BlockSelection $ Just { blockId, blockType }

handleAction (BlocklyEvent event) = detectCodeChanges CodeChange event

handleAction ResizeWorkspace = do
  mState <- use _blocklyState
  for_ mState \{ blockly, workspace } ->
    liftEffect $ Blockly.resize blockly workspace

-- When blockly becames visible or unvisible, we call hideChaff to avoid a visual glitch
-- See PR https://github.com/input-output-hk/plutus/pull/2787
handleAction (VisibilityChanged _) = do
  mState <- use _blocklyState
  for_ mState \{ blockly } ->
    liftEffect $ Blockly.hideChaff blockly
