module View (render) where

import Types
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnLink, col_, container, empty, justifyContentBetween, mlAuto, mrAuto, navItem, navLink, navbar, navbarBrand, navbarExpand, navbarNav, navbarText, nbsp, row_)
import Chain (evaluationPane)
import Control.Monad.State (evalState)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (_Right, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Semiring (zero)
import Data.Tuple.Nested (type (/\), (/\))
import Editor.Types (_keyBindings)
import Editor.View (compileButton, editorFeedback, editorPreferencesSelect, editorView)
import Effect.Aff.Class (class MonadAff)
import Gists.View (gistControls)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, a, button, div, footer, img, nav, span, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Extra (mapComponent)
import Halogen.HTML.Properties (class_, classes, height, href, id_, src, target, width)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (_SourceCode)
import NavTabs (mainTabBar, viewContainer)
import Network.RemoteData (RemoteData(..), _Success)
import Playground.Types (ContractDemo(..))
import Prelude (const, ($), (<$>), (<<<))
import Schema.Types (mkInitialValue)
import Simulation (actionsErrorPane, simulationPane)
import StaticData (_contractDemoEditorContents)
import StaticData as StaticData

foreign import plutusLogo :: String

-- renders the whole page
render ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
render state =
  div
    [ class_ $ ClassName "frame" ]
    [ mainHeader
    , subHeader state
    , mainContent state
    , mainFooter
    ]

-- renders the page header
mainHeader :: forall p. HTML p HAction
mainHeader =
  nav
    [ classes [ navbar, navbarExpand, justifyContentBetween, ClassName "header" ]
    ]
    [ span [ class_ navbarBrand ]
        [ img
            [ height 22
            , width 22
            , src plutusLogo
            ]
        , text
            "Plutus Playground"
        ]
    , documentationLinksPane
    ]

-- renders the documentation links
documentationLinksPane :: forall p i. HTML p i
documentationLinksPane =
  div
    [ id_ "docs"
    , classes [ navbarNav ]
    ]
    (makeNavItem <$> links)
  where
  links =
    [ text "Getting Started" /\ "https://testnet.iohkdev.io/plutus/get-started/writing-contracts-in-plutus/"
    , text "Tutorial" /\ "./tutorial/index.html"
    , text "API" /\ "./tutorial/haddock/index.html"
    , text "Privacy" /\ "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
    ]

-- renders the page sub header
subHeader ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
subHeader state@(State { contractDemos }) =
  nav
    [ classes [ navbar, navbarExpand, justifyContentBetween, ClassName "sub-header" ]
    ]
    [ contractDemosPane contractDemos
    , GistAction <$> gistControls (unwrap state)
    ]

-- renders the contract demos pane
contractDemosPane :: forall p. Array ContractDemo -> HTML p HAction
contractDemosPane contractDemos =
  div
    [ id_ "demos"
    , classes [ navbarNav ]
    ]
    ( Array.cons
        ( div [ class_ navbarText ]
            [ text "Demos:" ]
        )
        (demoScriptButton <$> contractDemos)
    )

-- renders a demo button
demoScriptButton :: forall p. ContractDemo -> HTML p HAction
demoScriptButton (ContractDemo { contractDemoName }) =
  button
    [ classes [ btn, btnLink ]
    , onClick $ const $ Just $ LoadScript contractDemoName
    ]
    [ text contractDemoName ]

-- renders the page content (editor, simulation, and transactions)
mainContent ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
mainContent state@(State { currentView }) =
  div
    [ id_ "main-content"
    , class_ container
    ]
    [ row_
        [ col_ [ mainTabBar ChangeView tabs currentView ] ]
    , row_
        [ editorTabPane state
        , simulationTabPane state
        , transactionsTabPane state
        ]
    ]
  where
  tabs ::
    Array
      { link :: View
      , title :: String
      }
  tabs =
    [ { link: Editor
      , title: "Editor"
      }
    , { link: Simulations
      , title: "Simulation"
      }
    , { link: Transactions
      , title: "Transactions"
      }
    ]

-- renders the editor tab pane
editorTabPane ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
editorTabPane state@(State { currentView, contractDemos, editorState }) =
  viewContainer currentView Editor
    let
      compilationResult = view _compilationResult state
    in
      [ div [ class_ $ ClassName "editor" ]
          [ div [ class_ $ ClassName "editor-controls" ]
              [ mapComponent EditorAction $ editorPreferencesSelect (view _keyBindings editorState)
              , compileButton CompileProgram compilationResult
              ]
          , mapComponent EditorAction $ editorView defaultContents StaticData.bufferLocalStorageKey editorState
          , mapComponent EditorAction $ editorFeedback compilationResult
          ]
      ]
  where
  defaultContents :: Maybe String
  defaultContents = view (_contractDemoEditorContents <<< _SourceCode) <$> StaticData.lookup "Vesting" contractDemos

-- renders the simulation tab pane
simulationTabPane ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
simulationTabPane state@(State { currentView }) =
  viewContainer currentView Simulations
    $ let
        knownCurrencies = evalState getKnownCurrencies state

        initialValue = mkInitialValue knownCurrencies zero
      in
        [ simulationPane
            initialValue
            (view _actionDrag state)
            ( view
                ( _compilationResult
                    <<< _Success
                    <<< _Right
                    <<< _Newtype
                    <<< _result
                    <<< _functionSchema
                )
                state
            )
            (view _simulations state)
            (view _evaluationResult state)
        , case (view _evaluationResult state) of
            Failure error -> ajaxErrorPane error
            Success (Left error) -> actionsErrorPane error
            _ -> empty
        ]

-- renders the transactions tab pane
transactionsTabPane ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
transactionsTabPane state@(State { currentView, blockchainVisualisationState }) =
  viewContainer currentView Transactions
    $ case view _evaluationResult state of
        Success (Right evaluation) -> [ evaluationPane blockchainVisualisationState evaluation ]
        Success (Left error) ->
          [ text "Your simulation has errors. Click the "
          , strong_ [ text "Simulation" ]
          , text " tab above to fix them and recompile."
          ]
        Failure error ->
          [ text "Your simulation has errors. Click the "
          , strong_ [ text "Simulation" ]
          , text " tab above to fix them and recompile."
          ]
        Loading -> [ icon Spinner ]
        NotAsked ->
          [ text "Click the "
          , strong_ [ text "Simulation" ]
          , text " tab above and evaluate a simulation to see some results."
          ]

-- renders the page footer
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

-- renders a link
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

-- copyright symbol
copyright :: forall p i. HTML p i
copyright = text "\x00A9"
