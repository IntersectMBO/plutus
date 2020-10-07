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
import Data.Traversable (for, for_)
import Effect (Effect)
import Effect.Class (class MonadEffect)
import Foreign.Generic (encodeJSON)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, raise)
import Halogen as H
import Halogen.Classes (aHorizontal, expanded, panelSubHeader, panelSubHeaderMain, sidebarComposer, hide, alignedButtonInTheMiddle, alignedButtonLast)
import Halogen.HTML (HTML, button, div, text, iframe, aside, section)
import Halogen.HTML.Core (AttrName(..))
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, id_, ref, src, attr)
import Marlowe.ActusBlockly (buildGenerator, parseActusJsonCode)
import Prelude (Unit, bind, const, discard, map, pure, show, unit, ($), (<<<), (<>))

foreign import sendContractToShiny ::
  String ->
  Effect Unit

type BlocklyState
  = { actusBlocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    , showShiny :: Boolean
    }

_actusBlocklyState :: Lens' BlocklyState (Maybe BT.BlocklyState)
_actusBlocklyState = prop (SProxy :: SProxy "actusBlocklyState")

_generator :: Lens' BlocklyState (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' BlocklyState (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_showShiny :: Lens' BlocklyState Boolean
_showShiny = prop (SProxy :: SProxy "showShiny")

data BlocklyQuery a
  = Resize a
  | SetError String a
  | GetWorkspace (String -> a)
  | LoadWorkspace String a

data ContractFlavour
  = FS
  | F

data BlocklyAction
  = Inject String (Array BlockDefinition)
  | GetTerms ContractFlavour
  | RunAnalysis

data BlocklyMessage
  = Initialized
  | CurrentTerms ContractFlavour String

type DSL m a
  = HalogenM BlocklyState BlocklyAction () BlocklyMessage m a

blockly :: forall m. MonadEffect m => String -> Array BlockDefinition -> Component HTML BlocklyQuery Unit BlocklyMessage m
blockly rootBlockName blockDefinitions =
  mkComponent
    { initialState: const { actusBlocklyState: Nothing, generator: Nothing, errorMessage: Just "(Labs is an experimental feature)", showShiny: false }
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

handleQuery (GetWorkspace f) = do
  mState <- use _actusBlocklyState
  for mState \bs -> do
    let
      xml = Blockly.workspaceXML bs.blockly bs.workspace
    pure $ f xml

handleQuery (LoadWorkspace xml next) = do
  mState <- use _actusBlocklyState
  for_ mState \state ->
    pure
      $ ST.run do
          workspaceRef <- STRef.new state.workspace
          Blockly.loadWorkspace state.blockly workspaceRef xml
  assign _errorMessage Nothing
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

handleAction RunAnalysis = do
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
      case parseActusJsonCode contract of
        Left e -> assign _errorMessage $ Just e
        Right c -> do
          assign _showShiny true
          liftEffect $ sendContractToShiny $ encodeJSON c
  where
  unexpected s = "An unexpected error has occurred, please raise a support issue: " <> s

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. BlocklyState -> HTML p BlocklyAction
render state =
  div []
    [ section [ classes [ panelSubHeader, aHorizontal ] ]
        [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
            [ toCodeButton "Generate reactive contract"
            , toStaticCodeButton "Generate static contract"
            , runAnalysis
            , errorMessage state.errorMessage
            ]
        ]
    , div [ classes [ ClassName "code-panel" ] ]
        [ div
            [ ref blocklyRef
            , id_ "actusBlocklyWorkspace"
            , classes [ ClassName "actus-blockly-workspace", ClassName "code-editor" ]
            ]
            []
        , shiny state
        ]
    ]

shiny ::
  forall p.
  BlocklyState -> HTML p BlocklyAction
shiny state =
  aside [ classes ([ sidebarComposer, expanded false ] <> if state.showShiny then [] else [ hide ]) ]
    [ div [ attr (AttrName "style") "height: 100%;" ]
        [ iframe
            [ src "http://localhost:8081"
            , id_ "shiny"
            , attr (AttrName "frameborder") "0"
            , attr (AttrName "scrolling") "no"
            , attr (AttrName "style") "position: relative; height: 100%; width: 100%;"
            ]
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
    , classes ([ alignedButtonInTheMiddle ])
    ]
    [ text key ]

runAnalysis :: forall p. HTML p BlocklyAction
runAnalysis =
  button
    [ onClick $ const $ Just $ RunAnalysis
    , classes ([ alignedButtonLast, hide ]) --this feature is temporary disabled because shiny is not deployed yet
    ]
    [ text "Run Analysis" ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
