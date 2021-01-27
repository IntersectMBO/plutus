module Halogen.Blockly where

import Prelude hiding (div)
import Blockly (BlockDefinition, ElementId(..), XML, getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, newBlock, blockToCode)
import Blockly.Types as BT
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, set, use)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Traversable (for, for_)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, modify_)
import Halogen as H
import Halogen.BlocklyCommons (updateUnsavedChangesActionHandler, blocklyEvents)
import Halogen.HTML (HTML, div, text)
import Halogen.HTML.Properties (class_, classes, id_, ref)
import Marlowe.Blockly (buildBlocks, buildGenerator)
import Marlowe.Holes (Term(..))
import Marlowe.Parser as Parser
import Prim.TypeError (class Warn, Text)
import Text.Extra as Text
import Type.Proxy (Proxy(..))

type State
  = { blocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    , useEvents :: Boolean
    }

_blocklyState :: Lens' State (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_generator :: Lens' State (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_useEvents :: Lens' State Boolean
_useEvents = prop (SProxy :: SProxy "useEvents")

emptyState :: State
emptyState = { blocklyState: Nothing, generator: Nothing, errorMessage: Nothing, useEvents: false }

data Query a
  = Resize a
  | SetCode String a
  | SetError String a
  | GetWorkspace (XML -> a)
  | LoadWorkspace XML a
  | GetCode (String -> a)

data Action
  = Inject String (Array BlockDefinition)
  | SetData Unit
  | BlocklyEvent BT.BlocklyEvent

data Message
  = CodeChange

type DSL slots m a
  = HalogenM State Action slots Message m a

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
  DSL slots m Unit
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

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall r p action. { errorMessage :: Maybe String | r } -> HTML p action
render state =
  div []
    [ div
        [ ref blocklyRef
        , id_ "blocklyWorkspace"
        , classes [ ClassName "blockly-workspace", ClassName "container-fluid" ]
        ]
        [ errorMessage state.errorMessage ]
    ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
