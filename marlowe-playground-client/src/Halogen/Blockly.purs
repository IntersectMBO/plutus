module Halogen.Blockly where

import Blockly (BlockDefinition, ElementId(..), getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, newBlock, blockToCode)
import Blockly.Types as BT
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Control.Monad.State (modify_)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, use)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Effect.Class (class MonadEffect)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, raise)
import Halogen as H
import Halogen.HTML (HTML, button, div, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, id_, ref)
import Marlowe.Blockly (buildBlocks, buildGenerator)
import Marlowe.Holes (Term(..))
import Marlowe.Parser as Parser
import Prelude (Unit, bind, const, discard, map, pure, show, unit, zero, ($), (<<<), (<>))
import Text.Extra as Text
import Text.Pretty (pretty)
import Type.Proxy (Proxy(..))

type BlocklyState
  = { blocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    }

_blocklyState :: Lens' BlocklyState (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_generator :: Lens' BlocklyState (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' BlocklyState (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

data BlocklyQuery a
  = Resize a
  | SetCode String a
  | SetError String a

data BlocklyAction
  = Inject String (Array BlockDefinition)
  | SetData Unit
  | GetCode

data BlocklyMessage
  = Initialized
  | CurrentCode String

type Slots
  = ()

type DSL m a
  = HalogenM BlocklyState BlocklyAction Slots BlocklyMessage m a

blockly :: forall m. MonadEffect m => String -> Array BlockDefinition -> Component HTML BlocklyQuery Unit BlocklyMessage m
blockly rootBlockName blockDefinitions =
  mkComponent
    { initialState: const { blocklyState: Nothing, generator: Nothing, errorMessage: Nothing }
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

handleQuery :: forall m a. MonadEffect m => BlocklyQuery a -> DSL m (Maybe a)
handleQuery (Resize next) = do
  mState <- use _blocklyState
  case mState of
    Just state ->
      pure
        $ ST.run
            ( do
                workspaceRef <- STRef.new state.workspace
                Blockly.resize state.blockly workspaceRef
            )
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

handleAction :: forall m. MonadEffect m => BlocklyAction -> DSL m Unit
handleAction (Inject rootBlockName blockDefinitions) = do
  blocklyState <- liftEffect $ Blockly.createBlocklyInstance rootBlockName (ElementId "blocklyWorkspace") (ElementId "blocklyToolbox")
  let
    _ =
      ST.run
        ( do
            blocklyRef <- STRef.new blocklyState.blockly
            workspaceRef <- STRef.new blocklyState.workspace
            Blockly.addBlockTypes blocklyRef blockDefinitions
            Blockly.initializeWorkspace blocklyState.blockly workspaceRef
        )

    generator = buildGenerator blocklyState
  modify_ _ { blocklyState = Just blocklyState, generator = Just generator }

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
      code <- except <<< lmap (const "This workspace cannot be converted to code") $ blockToCode block generator
      except <<< lmap (unexpected <<< show) $ Parser.parseContract (Text.stripParens code)
  case res of
    Left e -> assign _errorMessage $ Just e
    Right contract -> do
      assign _errorMessage Nothing
      raise <<< CurrentCode <<< show <<< pretty $ contract
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue: " <> s

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. BlocklyState -> HTML p BlocklyAction
render state =
  div []
    [ div
        [ ref blocklyRef
        , id_ "blocklyWorkspace"
        , classes [ ClassName "blockly-workspace", ClassName "container-fluid" ]
        ]
        [ toCodeButton "Send To Simulator"
        , errorMessage state.errorMessage
        ]
    ]

toCodeButton :: forall p. String -> HTML p BlocklyAction
toCodeButton key =
  button
    [ onClick $ const $ Just GetCode
    ]
    [ text key ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
