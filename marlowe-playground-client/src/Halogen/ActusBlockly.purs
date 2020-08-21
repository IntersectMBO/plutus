module Halogen.ActusBlockly where

import Blockly (BlockDefinition, ElementId(..), getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, blockToCode)
import Blockly.Types as BT
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
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
import Marlowe.ActusBlockly (buildGenerator)
import Prelude (Unit, bind, const, discard, map, pure, show, unit, ($), (<<<), (<>))

type BlocklyState
  = { actusBlocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    }

_actusBlocklyState :: Lens' BlocklyState (Maybe BT.BlocklyState)
_actusBlocklyState = prop (SProxy :: SProxy "actusBlocklyState")

_generator :: Lens' BlocklyState (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' BlocklyState (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

data BlocklyQuery a
  = Resize a
  | SetError String a

data ContractFlavour
  = FS
  | F

data BlocklyAction
  = Inject String (Array BlockDefinition)
  | GetTerms ContractFlavour

data BlocklyMessage
  = Initialized
  | CurrentTerms ContractFlavour String

type DSL m a
  = HalogenM BlocklyState BlocklyAction () BlocklyMessage m a

blockly :: forall m. MonadEffect m => String -> Array BlockDefinition -> Component HTML BlocklyQuery Unit BlocklyMessage m
blockly rootBlockName blockDefinitions =
  mkComponent
    { initialState: const { actusBlocklyState: Nothing, generator: Nothing, errorMessage: Nothing }
    , render
    , eval:
      H.mkEval
        { handleQuery
        , handleAction
        , initialize: Just $ Inject rootBlockName blockDefinitions
        , finalize: Nothing
        , receive: const Nothing
        }
    }

handleQuery :: forall m a. MonadEffect m => BlocklyQuery a -> DSL m (Maybe a)
handleQuery (Resize next) = do
  mState <- use _actusBlocklyState
  case mState of
    Just state ->
      pure
        $ ST.run do
            workspaceRef <- STRef.new state.workspace
            Blockly.resize state.blockly workspaceRef
    Nothing -> pure unit
  pure $ Just next

handleQuery (SetError err next) = do
  assign _errorMessage $ Just err
  pure $ Just next

handleAction :: forall m. MonadEffect m => BlocklyAction -> DSL m Unit
handleAction (Inject rootBlockName blockDefinitions) = do
  blocklyState <- liftEffect $ Blockly.createBlocklyInstance rootBlockName (ElementId "actusBlocklyWorkspace") (ElementId "actusBlocklyToolbox")
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
  assign _actusBlocklyState (Just blocklyState)
  assign _generator (Just generator)

handleAction (GetTerms flavour) = do
  res <-
    runExceptT do
      blocklyState <- ExceptT <<< map (note $ unexpected "BlocklyState not set") $ use _actusBlocklyState
      generator <- ExceptT <<< map (note $ unexpected "Generator not set") $ use _generator
      let
        workspace = blocklyState.workspace

        rootBlockName = blocklyState.rootBlockName
      block <- except <<< (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
      except <<< lmap (\x -> "This workspace cannot be converted to code: " <> (show x)) $ blockToCode block generator
  case res of
    Left e -> assign _errorMessage $ Just e
    Right contract -> do
      assign _errorMessage Nothing
      raise $ CurrentTerms flavour $ contract
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue: " <> s

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. BlocklyState -> HTML p BlocklyAction
render state =
  div []
    [ div
        [ ref blocklyRef
        , id_ "actusBlocklyWorkspace"
        , classes [ ClassName "actus-blockly-workspace", ClassName "container-fluid" ]
        ]
        [ toCodeButton "Generate reactive contract"
        , text "  "
        , toStaticCodeButton "Generate static contract"
        , text "  (Labs is an experimental feature)"
        , errorMessage state.errorMessage
        ]
    ]

toCodeButton :: forall p. String -> HTML p BlocklyAction
toCodeButton key =
  button
    [ onClick $ const $ Just $ GetTerms FS
    ]
    [ text key ]

toStaticCodeButton :: forall p. String -> HTML p BlocklyAction
toStaticCodeButton key =
  button
    [ onClick $ const $ Just $ GetTerms F
    ]
    [ text key ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
