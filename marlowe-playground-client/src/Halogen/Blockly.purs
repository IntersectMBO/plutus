module Halogen.Blockly where

import Blockly (BlockDefinition, ElementId(..), XML, addChangeListener, getBlockById, removeChangeListener)
import Blockly as Blockly
import Blockly.ChangeEvent as ChangeEvent
import Blockly.CreateEvent as CreateEvent
import Blockly.Generator (Generator, newBlock, blockToCode)
import Blockly.MoveEvent as MoveEvent
import Blockly.Types (Workspace)
import Blockly.Types as BT
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, set, use)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), isJust)
import Data.Symbol (SProxy(..))
import Data.Traversable (for, for_)
import Debug.Trace (spy)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, modify_, raise)
import Halogen as H
import Halogen.HTML (HTML, button, div, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, id_, ref)
import Halogen.Query.EventSource (EventSource)
import Halogen.Query.EventSource as EventSource
import Marlowe.Blockly (buildBlocks, buildGenerator)
import Marlowe.Holes (Term(..))
import Marlowe.Parser as Parser
import Prelude (Unit, bind, const, discard, map, pure, show, unit, void, zero, ($), (<<<), (<>), (||))
import Text.Extra as Text
import Text.Pretty (pretty)
import Type.Proxy (Proxy(..))
import Web.Event.EventTarget (eventListener)

type State
  = { blocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    }

_blocklyState :: Lens' State (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_generator :: Lens' State (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

emptyState :: State
emptyState = { blocklyState: Nothing, generator: Nothing, errorMessage: Nothing }

data Query a
  = Resize a
  | SetCode String a
  | SetError String a
  | GetWorkspace (XML -> a)
  | LoadWorkspace XML a
  | GetCodeQuery a

data Action
  = Inject String (Array BlockDefinition)
  | SetData Unit
  | BlocklyEvent
  | GetCode

data Message
  = CurrentCode String
  | CodeChange

type DSL slots m a
  = HalogenM State Action slots Message m a

blockly :: forall m. MonadAff m => String -> Array BlockDefinition -> Component HTML Query Unit Message m
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

handleQuery :: forall slots m a. MonadEffect m => Query a -> DSL slots m (Maybe a)
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
    Just bs -> do
      let
        contract = case Parser.parseContract code of
          Right c -> c
          Left _ -> Hole bs.rootBlockName Proxy zero
      pure $ ST.run (buildBlocks newBlock bs contract)
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

handleQuery (GetCodeQuery next) = do
  res <-
    runExceptT do
      blocklyState <- ExceptT <<< map (note $ unexpected "BlocklyState not set") $ use _blocklyState
      generator <- ExceptT <<< map (note $ unexpected "Generator not set") $ use _generator
      let
        workspace = blocklyState.workspace

        rootBlockName = blocklyState.rootBlockName
      block <- except <<< (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
      code <- except <<< lmap unexpected $ blockToCode block generator
      except <<< lmap (unexpected <<< show) $ Parser.parseContract (Text.stripParens code)
  case res of
    Left e -> assign _errorMessage $ Just e
    Right contract -> do
      assign _errorMessage Nothing
      raise <<< CurrentCode <<< show <<< pretty $ contract
  pure $ Just next
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleAction :: forall m slots. MonadAff m => Action -> DSL slots m Unit
handleAction (Inject rootBlockName blockDefinitions) = do
  blocklyState <- liftEffect $ Blockly.createBlocklyInstance rootBlockName (ElementId "blocklyWorkspace") (ElementId "blocklyToolbox")
  let
    _ =
      -- TODO: Refactor blockly to use Effect instead of ST
      -- https://github.com/input-output-hk/plutus/pull/2498#discussion_r533371159
      ST.run
        ( do
            blocklyRef <- STRef.new blocklyState.blockly
            workspaceRef <- STRef.new blocklyState.workspace
            Blockly.addBlockTypes blocklyRef blockDefinitions
            Blockly.initializeWorkspace blocklyState.blockly workspaceRef
        )

    generator = buildGenerator blocklyState
  void $ H.subscribe $ blocklyChanges blocklyState.workspace
  modify_
    ( set _blocklyState (Just blocklyState)
        <<< set _generator (Just generator)
    )

handleAction (SetData _) = pure unit

handleAction GetCode = do
  res <-
    runExceptT do
      blocklyState <- ExceptT <<< map (note $ unexpected "BlocklyState not set") $ use _blocklyState
      generator <- ExceptT <<< map (note $ unexpected "Generator not set") $ use _generator
      let
        workspace = blocklyState.workspace

        rootBlockName = blocklyState.rootBlockName
      block <- except <<< (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
      code <- except <<< lmap unexpected $ blockToCode block generator
      except <<< lmap (unexpected <<< show) $ Parser.parseContract (Text.stripParens code)
  case res of
    Left e -> assign _errorMessage $ Just e
    Right contract -> do
      assign _errorMessage Nothing
      raise <<< CurrentCode <<< show <<< pretty $ contract
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue at https://github.com/input-output-hk/plutus/issues/new: " <> s

handleAction BlocklyEvent = raise CodeChange

blocklyChanges :: forall m. MonadAff m => Workspace -> EventSource m Action
blocklyChanges workspace =
  EventSource.effectEventSource \emitter -> do
    listener <-
      eventListener \event ->
        let
          isCreateEvent = isJust $ CreateEvent.fromEvent $ spy "BlocklyEvent" event

          isMoveEvent = isJust $ MoveEvent.fromEvent event

          isChangeEvent = isJust $ ChangeEvent.fromEvent event
        -- Blockly can fire all of the following events https://developers.google.com/blockly/guides/configure/web/events
        -- but we only care for the ones that may change the contract.
        -- TODO: the move event by its own shouldn't necesarly cause a change in the contract
        -- we should check if the string property "newParentId" is defined
        in
          if isCreateEvent || isMoveEvent || isChangeEvent then
            EventSource.emit emitter BlocklyEvent
          else
            pure unit
    addChangeListener workspace listener
    pure $ EventSource.Finalizer $ removeChangeListener workspace listener

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. State -> HTML p Action
render state =
  div []
    [ div
        [ ref blocklyRef
        , id_ "blocklyWorkspace"
        , classes [ ClassName "blockly-workspace", ClassName "container-fluid" ]
        ]
        [ errorMessage state.errorMessage ]
    ]

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div []
    [ toCodeButton "Send To Simulator"
    ]

toCodeButton :: forall p. String -> HTML p Action
toCodeButton key =
  button
    [ onClick $ const $ Just GetCode
    ]
    [ text key ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
