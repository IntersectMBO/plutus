module Halogen.ActusBlockly where

import Prelude hiding (div)
import Blockly (BlockDefinition, ElementId(..), XML, getBlockById)
import Blockly as Blockly
import Blockly.Generator (Generator, blockToCode)
import Blockly.Types as BT
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Control.Monad.ST as ST
import Control.Monad.ST.Ref as STRef
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, set, use)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.Symbol (SProxy(..))
import Data.Traversable (for, for_)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Foreign.Generic (encodeJSON)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, modify_, raise)
import Halogen as H
import Halogen.BlocklyCommons (blocklyEvents, updateUnsavedChangesActionHandler)
import Halogen.Classes (aHorizontal, expanded, panelSubHeader, panelSubHeaderMain, sidebarComposer, hide, alignedButtonInTheMiddle, alignedButtonLast)
import Halogen.HTML (HTML, button, div, text, iframe, aside, section)
import Halogen.HTML.Core (AttrName(..))
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, id_, ref, src, attr)
import Marlowe.ActusBlockly (buildGenerator, parseActusJsonCode)

foreign import sendContractToShiny ::
  String ->
  Effect Unit

type State
  = { actusBlocklyState :: Maybe BT.BlocklyState
    , generator :: Maybe Generator
    , errorMessage :: Maybe String
    , showShiny :: Boolean
    , useEvents :: Boolean
    }

_actusBlocklyState :: Lens' State (Maybe BT.BlocklyState)
_actusBlocklyState = prop (SProxy :: SProxy "actusBlocklyState")

_generator :: Lens' State (Maybe Generator)
_generator = prop (SProxy :: SProxy "generator")

_errorMessage :: Lens' State (Maybe String)
_errorMessage = prop (SProxy :: SProxy "errorMessage")

_showShiny :: Lens' State Boolean
_showShiny = prop (SProxy :: SProxy "showShiny")

data Query a
  = Resize a
  | SetError String a
  | GetWorkspace (XML -> a)
  | LoadWorkspace XML a

data ContractFlavour
  = FS
  | F

data Action
  = Inject String (Array BlockDefinition)
  | GetTerms ContractFlavour
  | BlocklyEvent BT.BlocklyEvent
  | RunAnalysis

data Message
  = Initialized
  | CurrentTerms ContractFlavour String
  | CodeChange

type DSL m a
  = HalogenM State Action () Message m a

blockly :: forall m. MonadAff m => String -> Array BlockDefinition -> Component HTML Query Unit Message m
blockly rootBlockName blockDefinitions =
  mkComponent
    { initialState:
        const
          { actusBlocklyState: Nothing
          , generator: Nothing
          , errorMessage: Just "(Labs is an experimental feature)"
          , showShiny: false
          , useEvents: false
          }
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

handleQuery :: forall m a. MonadEffect m => Query a -> DSL m (Maybe a)
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

handleAction :: forall m. MonadAff m => Action -> DSL m Unit
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
  void $ H.subscribe $ blocklyEvents BlocklyEvent blocklyState.workspace
  modify_
    ( set _actusBlocklyState (Just blocklyState)
        <<< set _generator (Just generator)
    )

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
      case parseActusJsonCode contract of
        Left e -> assign _errorMessage $ Just e
        Right ctRaw -> do
          let
            ct = (unwrap ctRaw)
          case flavour of
            F ->
              if (isJust ct.ct_RRCL) then
                assign _errorMessage $ Just "Rate resets are not allowed in static contracts"
              else
                raise $ CurrentTerms flavour $ contract
            _ -> raise $ CurrentTerms flavour $ contract
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

handleAction (BlocklyEvent event) = updateUnsavedChangesActionHandler CodeChange event

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. State -> HTML p Action
render state =
  div []
    [ section [ classes [ panelSubHeader, aHorizontal ] ]
        [ div [ classes [ panelSubHeaderMain, aHorizontal, ClassName "actus-buttons" ] ]
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
  State -> HTML p Action
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

toCodeButton :: forall p. String -> HTML p Action
toCodeButton key =
  button
    [ onClick $ const $ Just $ GetTerms FS
    ]
    [ text key ]

toStaticCodeButton :: forall p. String -> HTML p Action
toStaticCodeButton key =
  button
    [ onClick $ const $ Just $ GetTerms F
    , classes ([ alignedButtonInTheMiddle ])
    ]
    [ text key ]

runAnalysis :: forall p. HTML p Action
runAnalysis =
  button
    [ onClick $ const $ Just $ RunAnalysis
    , classes ([ alignedButtonLast, hide ]) --this feature is temporary disabled because shiny is not deployed yet
    ]
    [ text "Run Analysis" ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
