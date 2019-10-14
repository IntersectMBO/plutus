module Halogen.Blockly where

import Blockly (BlockDefinition, ElementId(..))
import Blockly as Blockly
import Blockly.Generator (Generator, newBlock, workspaceToCode)
import Blockly.Types as BT
import Bootstrap (btn, btnInfo, btnSmall)
import Control.Alt ((<|>))
import Control.Monad.Except (ExceptT(..), runExceptT, lift)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, use)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.NaturalTransformation (type (~>))
import Data.Symbol (SProxy(..))
import Effect.Class (class MonadEffect)
import Halogen (ClassName(..), Component, ComponentDSL, ComponentHTML, RefLabel(..), action, get, lifecycleComponent, liftEffect, modify, raise)
import Halogen.HTML (button, div, text)
import Halogen.HTML as HH
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (class_, classes, id_, ref)
import Marlowe.Blockly (buildBlocks, buildGenerator)
import Marlowe.Parser as Parser
import Marlowe.Pretty (pretty)
import Marlowe.Semantics (Contract(..))
import Prelude (Unit, bind, discard, pure, show, unit, ($), map, (<>), (<<<), const)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Basic (parens)

type BlocklyState
  = { blocklyState :: Maybe BT.BlocklyState, generator :: Maybe Generator, errorMessage :: Maybe String }

_blocklyState :: Lens' BlocklyState (Maybe BT.BlocklyState)
_blocklyState = prop (SProxy :: SProxy "blocklyState")

_generator :: Lens' BlocklyState (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' BlocklyState (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

data BlocklyQuery a
  = Inject (Array BlockDefinition) a
  | Resize a
  | SetData Unit a
  | GetCode a
  | SetCode String a

data BlocklyMessage
  = Initialized
  | CurrentCode String

type HTML
  = ComponentHTML BlocklyQuery

type DSL m
  = ComponentDSL BlocklyState BlocklyQuery BlocklyMessage m

blockly :: forall m. MonadEffect m => Array BlockDefinition -> Component HH.HTML BlocklyQuery Unit BlocklyMessage m
blockly blockDefinitions =
  lifecycleComponent
    { initialState: \_ -> { blocklyState: Nothing, generator: Nothing, errorMessage: Nothing }
    , render
    , eval
    , initializer: Just $ action (Inject blockDefinitions)
    , finalizer: Nothing
    , receiver: HE.input SetData
    }

eval :: forall m. MonadEffect m => BlocklyQuery ~> DSL m
eval (Inject blockDefinitions next) = do
  blocklyState <- liftEffect $ Blockly.createBlocklyInstance (ElementId "blocklyWorkspace") (ElementId "blocklyToolbox")
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
  _ <- modify _ { blocklyState = Just blocklyState, generator = Just generator }
  pure next

eval (Resize next) = do
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
  pure next

eval (SetData _ next) = pure next

eval (GetCode next) = do
  res <-
    runExceptT do
      blocklyState <- ExceptT <<< map (note $ unexpected "BlocklyState not set") $ use _blocklyState
      generator <- ExceptT <<< map (note $ unexpected "Generator not set") $ use _generator
      code <- ExceptT <<< pure <<< lmap (const "This workspace cannot be converted to code") $ workspaceToCode blocklyState generator
      contract <- ExceptT <<< pure <<< lmap (unexpected <<< show) $ runParser code (parens Parser.contract <|> Parser.contract)
      lift <<< raise <<< CurrentCode <<< show <<< pretty $ contract
  case res of
    Left e -> assign _errorMessage $ Just e
    Right _ -> assign _errorMessage Nothing
  pure next
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue: " <> s

eval (SetCode code next) = do
  { blocklyState } <- get
  let
    contract = case runParser code Parser.contract of
      Right c -> c
      Left _ -> Close
  case blocklyState of
    Nothing -> pure unit
    Just bs -> pure $ ST.run (buildBlocks newBlock bs contract)
  assign _errorMessage Nothing
  pure next

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: BlocklyState -> HTML
render state =
  div []
    [ div
        [ ref blocklyRef
        , id_ "blocklyWorkspace"
        , classes [ ClassName "blockly-workspace", ClassName "container-fluid" ]
        ]
        [ toCodeButton "To Code"
        , errorMessage state.errorMessage
        ]
    ]

toCodeButton :: String -> HTML
toCodeButton key =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ input_ GetCode
    ]
    [ text key ]

errorMessage :: Maybe String -> HTML
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
