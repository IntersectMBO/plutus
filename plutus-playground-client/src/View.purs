module View (render) where

import Bootstrap (active, btn, containerFluid, hidden, justifyContentBetween, mlAuto, mrAuto, navItem, navLink, navbar, navbarBrand, navbarExpand, navbarNav, navbarText, nbsp)
import Chain (evaluationPane)
import Chain.Types as Chain
import Control.Monad.State (evalState)
import Cursor (Cursor)
import Data.Either (Either(..))
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Semiring (zero)
import Data.Tuple.Nested (type (/\), (/\))
import Editor.Types (_currentCodeIsCompiled, _keyBindings)
import Editor.Types as Editor
import Editor.View (compileButton, editorPreferencesSelect, simulateButton, editorPane, editorFeedback)
import Effect.Aff.Class (class MonadAff)
import Gists.View (gistControls)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, a, button, div, footer, h1_, img, label_, main, nav, span, strong_, text, ul, li)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Extra (mapComponent)
import Halogen.HTML.Properties (class_, classes, height, href, src, target, width)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (_SourceCode)
import Network.RemoteData (RemoteData(..))
import Playground.Types (ContractDemo(..), Simulation)
import Prelude (class Eq, const, ($), (<$>), (<<<), (==))
import Schema.Types (mkInitialValue)
import Simulation (simulatorTitle, simulationsPane, simulationsNav)
import StaticData (_contractDemoEditorContents)
import StaticData as StaticData
import Types (ChildSlots, HAction(..), State(..), View(..), WebCompilationResult, WebEvaluationResult, getKnownCurrencies)

foreign import plutusLogo :: String

render :: forall m. MonadAff m => State -> ComponentHTML HAction ChildSlots m
render state@(State { contractDemos, currentView, editorState, compilationResult, simulations, evaluationResult, blockchainVisualisationState }) =
  div
    [ class_ $ ClassName "frame" ]
    [ mainHeader
    , subHeader state
    , editorMain contractDemos currentView editorState compilationResult
    , simulationsMain state
    , transactionsMain currentView simulations evaluationResult blockchainVisualisationState
    , mainFooter
    ]

mainHeader :: forall p. HTML p HAction
mainHeader =
  nav
    [ classes [ navbar, navbarExpand, justifyContentBetween, ClassName "header" ]
    ]
    [ span [ class_ navbarBrand ]
        [ img
            [ height 36
            , width 36
            , src plutusLogo
            ]
        , text
            "Plutus playground"
        ]
    , documentationLinksPane
    ]

documentationLinksPane :: forall p i. HTML p i
documentationLinksPane =
  ul
    [ class_ navbarNav ]
    (makeNavItem <$> links)
  where
  links =
    [ text "Getting Started" /\ "https://testnet.iohkdev.io/plutus/get-started/writing-contracts-in-plutus/"
    , text "Tutorial" /\ "./tutorial/index.html"
    , text "API" /\ "./tutorial/haddock/index.html"
    , text "Privacy" /\ "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
    ]

subHeader :: forall m. MonadAff m => State -> ComponentHTML HAction ChildSlots m
subHeader state@(State { demoFilesMenuOpen, contractDemos, currentDemoName }) =
  nav
    [ classes [ navbar, navbarExpand, justifyContentBetween, ClassName "sub-header" ] ]
    [ a
        [ classes buttonClasses
        , onClick $ const $ Just $ ToggleDemoFilesMenu
        ]
        [ buttonIcon ]
    , contractDemosPane demoFilesMenuOpen contractDemos currentDemoName
    , GistAction <$> gistControls (unwrap state)
    ]
  where
  buttonClasses =
    if demoFilesMenuOpen then
      [ btn, buttonClass, ClassName "open" ]
    else
      [ btn, buttonClass ]

  buttonClass = ClassName "menu-button"

  buttonIcon =
    if demoFilesMenuOpen then
      icon Close
    else
      icon Bars

contractDemosPane :: forall p. Boolean -> Array ContractDemo -> Maybe String -> HTML p HAction
contractDemosPane demoFilesMenuOpen contractDemos currentDemoName =
  div
    [ classes demoPaneClasses ]
    [ span
        [ class_ navbarText ]
        [ text "Demo files" ]
    , ul
        [ class_ navbarNav ]
        (demoScriptNavItem currentDemoName <$> contractDemos)
    ]
  where
  demoPaneClasses =
    if demoFilesMenuOpen then
      [ navbarNav, ClassName "menu", ClassName "open" ]
    else
      [ navbarNav, ClassName "menu" ]

demoScriptNavItem :: forall p. Maybe String -> ContractDemo -> HTML p HAction
demoScriptNavItem currentDemoName (ContractDemo { contractDemoName }) =
  li
    [ class_ navItem ]
    [ a
        [ classes navLinkClasses
        , onClick $ const $ Just $ LoadScript contractDemoName
        ]
        [ text contractDemoName ]
    ]
  where
  navLinkClasses = case currentDemoName of
    Just name ->
      if contractDemoName == name then
        [ active, navLink ]
      else
        [ navLink ]
    Nothing -> [ navLink ]

editorMain :: forall m. MonadAff m => Array ContractDemo -> View -> Editor.State -> WebCompilationResult -> ComponentHTML HAction ChildSlots m
editorMain contractDemos currentView editorState compilationResult =
  main
    [ classes $ mainComponentClasses currentView Editor ]
    [ div
        [ class_ $ ClassName "main-header" ]
        [ h1_ [ text "Editor" ]
        , button [ classes [ btn, ClassName "hidden" ] ] [ nbsp ]
        ] -- invisible button so the height matches the simulator header
    , editorWrapper contractDemos currentView editorState compilationResult
    ]

simulationsMain :: forall m. MonadAff m => State -> ComponentHTML HAction ChildSlots m
simulationsMain state@(State { currentView }) =
  main
    [ classes $ mainComponentClasses currentView Simulations ]
    [ simulatorTitle
    , simulationsWrapper state
    ]

transactionsMain :: forall m. MonadAff m => View -> Cursor Simulation -> WebEvaluationResult -> Chain.State -> ComponentHTML HAction ChildSlots m
transactionsMain currentView simulations evaluationResult blockchainVisualisationState =
  main
    [ classes $ mainComponentClasses currentView Transactions ]
    [ simulatorTitle
    , transactionsWrapper simulations evaluationResult blockchainVisualisationState
    ]

mainComponentClasses :: forall view. Eq view => view -> view -> Array (ClassName)
mainComponentClasses currentView targetView =
  if currentView == targetView then
    [ containerFluid, ClassName "main" ]
  else
    [ containerFluid, hidden, ClassName "main" ]

editorWrapper :: forall m. MonadAff m => Array ContractDemo -> View -> Editor.State -> WebCompilationResult -> ComponentHTML HAction ChildSlots m
editorWrapper contractDemos currentView editorState compilationResult =
  div
    [ classes [ ClassName "main-body", ClassName "editor" ] ]
    [ div
        [ class_ $ ClassName "editor-controls" ]
        [ div
            [ class_ $ ClassName "key-bindings" ]
            [ label_ [ text "Key Bindings" ]
            , mapComponent EditorAction $ editorPreferencesSelect (view _keyBindings editorState)
            ]
        , div
            [ class_ $ ClassName "editor-buttons" ]
            [ compileButton compilationResult
            , simulateButton (view _currentCodeIsCompiled editorState) compilationResult
            ]
        ]
    , mapComponent EditorAction $ editorPane defaultContents StaticData.bufferLocalStorageKey editorState
    , mapComponent EditorAction $ editorFeedback editorState compilationResult
    ]
  where
  defaultContents :: Maybe String
  defaultContents = view (_contractDemoEditorContents <<< _SourceCode) <$> StaticData.lookup "Vesting" contractDemos

simulationsWrapper :: forall p. State -> HTML p HAction
simulationsWrapper state@(State { actionDrag, currentView, compilationResult, simulations, lastEvaluatedSimulation, evaluationResult }) =
  let
    knownCurrencies = evalState getKnownCurrencies state

    initialValue = mkInitialValue knownCurrencies zero
  in
    div
      [ classes [ ClassName "main-body", ClassName "simulator" ] ]
      [ simulationsPane
          initialValue
          actionDrag
          compilationResult
          simulations
          lastEvaluatedSimulation
          evaluationResult
      ]

transactionsWrapper :: forall m. MonadAff m => Cursor Simulation -> WebEvaluationResult -> Chain.State -> ComponentHTML HAction ChildSlots m
transactionsWrapper simulations evaluationResult blockchainVisualisationState =
  div
    [ classes [ ClassName "main-body", ClassName "simulator" ] ]
    [ div
        [ class_ $ ClassName "simulations" ]
        [ simulationsNav simulations
        , div
            [ class_ $ ClassName "simulation" ] case evaluationResult of
            Success (Right evaluation) -> [ evaluationPane blockchainVisualisationState evaluation ]
            Success (Left error) ->
              [ text "Your simulation has errors. Click the "
              , strong_ [ text "Simulations" ]
              , text " tab above to fix them and recompile."
              ]
            Failure error ->
              [ text "Your simulation has errors. Click the "
              , strong_ [ text "Simulations" ]
              , text " tab above to fix them and recompile."
              ]
            Loading -> [ icon Spinner ]
            NotAsked ->
              [ text "Click the "
              , strong_ [ text "Simulations" ]
              , text " tab above and evaluate a simulation to see some results."
              ]
        ]
    ]

mainFooter :: forall p i. HTML p i
mainFooter =
  footer
    [ classes [ navbar, navbarExpand, ClassName "footer" ]
    ]
    [ div
        [ classes [ navbarNav, mrAuto ] ]
        [ makeNavItem $ text "cardano.org" /\ "https://cardano.org/"
        , makeNavItem $ text "iohk.io" /\ "https://iohk.io/"
        ]
    , div
        [ classes [ navbarNav ] ]
        [ copyright
        , nbsp
        , text "2020 IOHK Ltd."
        ]
    , div
        [ classes [ navbarNav, mlAuto ] ]
        [ makeNavItem $ text "Twitter" /\ "https://twitter.com/hashtag/Plutus" ]
    ]

makeNavItem :: forall p i. HTML p i /\ String -> HTML p i
makeNavItem (label /\ link) =
  span
    [ classes [ navItem ] ]
    [ a
        [ class_ navLink
        , href link
        , target "_blank"
        ]
        [ label ]
    ]

copyright :: forall p i. HTML p i
copyright = text "\x00A9"
