module Halogen.ActusBlockly where

import Prelude hiding (div)
import Blockly.Generator (Generator, blockToCode)
import Blockly.Internal (BlockDefinition, ElementId(..), XML, getBlockById)
import Blockly.Internal as Blockly
import Blockly.Toolbox (Toolbox)
import Blockly.Types as BT
import Bootstrap (btn)
import Control.Monad.Except (ExceptT(..), except, runExceptT)
import Data.Bifunctor (lmap)
import Data.Either (Either(..), note)
import Data.Lens (Lens', assign, set, use)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap)
import Data.Symbol (SProxy(..))
import Data.Traversable (for, for_)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Foreign.Generic (encodeJSON)
import Halogen (ClassName(..), Component, HalogenM, RefLabel(..), liftEffect, mkComponent, modify_, raise)
import Halogen as H
import Halogen.BlocklyCommons (blocklyEvents, detectCodeChanges)
import Halogen.Classes (aHorizontal, alignedButtonInTheMiddle, alignedButtonLast, expanded, flex, flexCol, flexGrow, fontBold, fullHeight, hidden, smallPaddingLeft, smallPaddingY, textInactive)
import Halogen.Css (classNames)
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
    , eventsWhileDragging :: Maybe (List BT.BlocklyEvent)
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

-- QUESTION:
-- QUESTION: What are the different ContractFlavour F and FS?
-- QUESTION:
data ContractFlavour
  = FS
  | F

data Action
  = Inject String (Array BlockDefinition) Toolbox
  | GetTerms ContractFlavour
  | BlocklyEvent BT.BlocklyEvent
  | RunAnalysis

data Message
  = Initialized
  | CurrentTerms ContractFlavour String
  | CodeChange

type DSL m a
  = HalogenM State Action () Message m a

-- FIXME: rename to mkBlockly to avoid shadowing in handleQuery
blockly ::
  forall m.
  MonadAff m =>
  String ->
  Array BlockDefinition ->
  Toolbox ->
  Component HTML Query Unit Message m
blockly rootBlockName blockDefinitions toolbox =
  mkComponent
    { initialState:
        const
          { actusBlocklyState: Nothing
          , generator: Nothing
          , errorMessage: Just "(Labs is an experimental feature)"
          , showShiny: false
          , eventsWhileDragging: Nothing
          }
    , render
    , eval:
        H.mkEval
          { handleQuery
          , handleAction
          , initialize: Just $ Inject rootBlockName blockDefinitions toolbox
          , finalize: Nothing
          , receive: const Nothing
          }
    }

handleQuery :: forall m a. MonadEffect m => Query a -> DSL m (Maybe a)
handleQuery (Resize next) = do
  mState <- use _actusBlocklyState
  for_ mState \{ blockly, workspace } ->
    liftEffect $ Blockly.resize blockly workspace
  pure $ Just next

handleQuery (SetError err next) = do
  assign _errorMessage $ Just err
  pure $ Just next

handleQuery (GetWorkspace f) = do
  mState <- use _actusBlocklyState
  for mState \bs -> do
    xml <- liftEffect $ Blockly.workspaceXML bs.blockly bs.workspace
    pure $ f xml

handleQuery (LoadWorkspace xml next) = do
  mState <- use _actusBlocklyState
  for_ mState \{ blockly, workspace } ->
    liftEffect $ Blockly.loadWorkspace blockly workspace xml
  assign _errorMessage Nothing
  pure $ Just next

handleAction :: forall m. MonadAff m => Action -> DSL m Unit
handleAction (Inject rootBlockName blockDefinitions toolbox) = do
  blocklyState /\ generator <-
    liftEffect do
      state <- Blockly.createBlocklyInstance rootBlockName (ElementId "actusBlocklyWorkspace") toolbox
      Blockly.addBlockTypes state.blockly blockDefinitions
      Blockly.initializeWorkspace state.blockly state.workspace
      generator <- buildGenerator state.blockly
      pure $ Tuple state generator
  void $ H.subscribe $ blocklyEvents BlocklyEvent blocklyState.workspace
  modify_
    ( set _actusBlocklyState (Just blocklyState)
        <<< set _generator (Just generator)
    )

handleAction (GetTerms flavour) = do
  mBlocklyState <- use _actusBlocklyState
  mGenerator <- use _generator
  res <-
    liftEffect
      $ runExceptT do
          { workspace, rootBlockName } <- except <<< (note $ unexpected "BlocklyState not set") $ mBlocklyState
          generator <- except <<< (note $ unexpected "Generator not set") $ mGenerator
          block <- ExceptT <<< map (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
          ExceptT $ lmap (\x -> "This workspace cannot be converted to code: " <> (show x)) <$> blockToCode block generator
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
  mBlocklyState <- use _actusBlocklyState
  mGenerator <- use _generator
  res <-
    liftEffect
      $ runExceptT do
          { workspace, rootBlockName } <- except <<< (note $ unexpected "BlocklyState not set") $ mBlocklyState
          generator <- except <<< (note $ unexpected "Generator not set") $ mGenerator
          block <- ExceptT <<< map (note $ unexpected ("Can't find root block" <> rootBlockName)) $ getBlockById workspace rootBlockName
          ExceptT $ lmap (\x -> "This workspace cannot be converted to code: " <> (show x)) <$> blockToCode block generator
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

handleAction (BlocklyEvent event) = detectCodeChanges CodeChange event

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall p. State -> HTML p Action
render state =
  div [ classes [ fullHeight, flex, flexCol ] ]
    [ section [ classes [ aHorizontal ] ]
        [ div [ classes [ smallPaddingY, smallPaddingLeft, aHorizontal, fontBold, textInactive ] ]
            [ toCodeButton "Generate reactive contract"
            , toStaticCodeButton "Generate static contract"
            , runAnalysis
            , errorMessage state.errorMessage
            ]
        ]
    , div
        [ ref blocklyRef
        , id_ "actusBlocklyWorkspace"
        , classes [ flexGrow ]
        ]
        []
    ]

shiny ::
  forall p.
  State -> HTML p Action
shiny state =
  aside [ classes ([ expanded false ] <> if state.showShiny then [] else [ hidden ]) ]
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
    , classNames [ "btn" ]
    ]
    [ text key ]

toStaticCodeButton :: forall p. String -> HTML p Action
toStaticCodeButton key =
  button
    [ onClick $ const $ Just $ GetTerms F
    , classes ([ alignedButtonInTheMiddle, btn ])
    ]
    [ text key ]

runAnalysis :: forall p. HTML p Action
runAnalysis =
  button
    [ onClick $ const $ Just $ RunAnalysis
    , classes ([ alignedButtonLast, hidden ]) --this feature is temporary disabled because shiny is not deployed yet
    ]
    [ text "Run Analysis" ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
