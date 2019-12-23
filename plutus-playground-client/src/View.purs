module View (render) where

import Types
import Action (actionsErrorPane, simulationPane)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (active, alert, alertPrimary, btn, btnGroup, btnInfo, btnSmall, col5_, col7_, colSm5, colSm6, colXs12, container, container_, empty, floatRight, hidden, justifyContentBetween, navItem_, navLink, navTabs_, noGutters, row, row_)
import Bootstrap as Bootstrap
import Chain (evaluationPane)
import Control.Monad.State (evalState)
import Data.Array (cons, find) as Array
import Data.Either (Either(..))
import Data.Json.JsonEither (JsonEither(..), _JsonEither)
import Data.Lens (_Right, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Editor (compileButton, editorFeedback, editorView)
import Effect.Aff.Class (class MonadAff)
import Gists (gistControls)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, a, br_, button, div, div_, h1, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Extra (mapComponent)
import Halogen.HTML.Properties (class_, classes, href, id_)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (_SourceCode)
import Network.RemoteData (RemoteData(..), _Success)
import Playground.Types (ContractDemo(..))
import Prelude (const, show, ($), (<$>), (<<<), (<>), (==))
import StaticData (_contractDemoEditorContents)
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
render state@(State { currentView, blockchainVisualisationState, contractDemos, editorPreferences }) =
  div_
    [ bannerMessage
    , div
        [ class_ $ ClassName "main-frame" ]
        [ container_
            [ mainHeader
            , div [ classes [ row, noGutters, justifyContentBetween ] ]
                [ div [ classes [ colXs12, colSm6 ] ] [ mainTabBar currentView ]
                , div
                    [ classes [ colXs12, colSm5 ] ]
                    [ GistAction <$> gistControls (unwrap state) ]
                ]
            ]
        , viewContainer currentView Editor
            let
              compilationResult = unwrap <$> view _compilationResult state
            in
              [ row_
                  [ col7_ [ compileButton CompileProgram compilationResult ]
                  , col5_ [ contractDemosPane contractDemos ]
                  ]
              , br_
              , mapComponent EditorAction $ editorView defaultContents _editorSlot StaticData.bufferLocalStorageKey editorPreferences
              , compileButton CompileProgram compilationResult
              , mapComponent EditorAction $ editorFeedback compilationResult
              , case compilationResult of
                  Failure error -> ajaxErrorPane error
                  _ -> empty
              ]
        , viewContainer currentView Simulations
            $ let
                knownCurrencies = evalState getKnownCurrencies state

                initialValue = mkInitialValue knownCurrencies 0
              in
                [ simulationPane
                    initialValue
                    (view _actionDrag state)
                    ( view
                        ( _compilationResult
                            <<< _Success
                            <<< _JsonEither
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
                    Success (JsonEither (Left error)) -> actionsErrorPane error
                    _ -> empty
                ]
        , viewContainer currentView Transactions
            $ case view _evaluationResult state of
                Success (JsonEither (Right evaluation)) -> [ evaluationPane blockchainVisualisationState evaluation ]
                Success (JsonEither (Left error)) ->
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
        ]
    ]
  where
  defaultContents :: Maybe String
  defaultContents = view (_contractDemoEditorContents <<< _SourceCode) <$> StaticData.lookup "Vesting" contractDemos

contractDemosPane :: forall p. Array ContractDemo -> HTML p HAction
contractDemosPane contractDemos =
  div [ id_ "demos" ]
    ( Array.cons (strong_ [ text "Demos: " ]) (demoScriptButton <$> contractDemos)
    )

demoScriptButton :: forall p. ContractDemo -> HTML p HAction
demoScriptButton (ContractDemo { contractDemoName }) =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ const $ Just $ LoadScript contractDemoName
    ]
    [ text contractDemoName ]

bannerMessage :: forall p i. HTML p i
bannerMessage =
  div
    [ id_ "banner-message"
    , classes [ alert, alertPrimary ]
    ]
    [ text "Plutus Beta - Updated 19th September 2019 - See the "
    , a
        [ href ("https://github.com/input-output-hk/plutus/blob/master/CHANGELOG.md") ]
        [ text "CHANGELOG" ]
    ]

viewContainer :: forall p i. View -> View -> Array (HTML p i) -> HTML p i
viewContainer currentView targetView =
  if currentView == targetView then
    div [ classes [ container ] ]
  else
    div [ classes [ container, hidden ] ]

mainHeader :: forall p. HTML p HAction
mainHeader =
  div_
    [ div [ classes [ btnGroup, floatRight ] ]
        (makeLink <$> links)
    , h1
        [ class_ $ ClassName "main-title" ]
        [ text "Plutus Playground" ]
    ]
  where
  links =
    [ Tuple "Getting Started" "https://testnet.iohkdev.io/plutus/get-started/writing-contracts-in-plutus/"
    , Tuple "Tutorial" "./tutorial"
    , Tuple "API" "./haddock"
    , Tuple "Privacy" "https://static.iohk.io/docs/data-protection/iohk-data-protection-gdpr-policy.pdf"
    ]

  makeLink (Tuple name link) =
    a
      [ classes [ btn, btnSmall ]
      , href link
      ]
      [ text name ]

mainTabBar :: forall p. View -> HTML p HAction
mainTabBar activeView =
  div_
    [ navTabs_ (mkTab <$> tabs)
    , div [ class_ $ ClassName "tab-help" ]
        [ helpText ]
    ]
  where
  tabs =
    [ { link: Editor
      , title: "Editor"
      , help: "Edit and compile your contract."
      }
    , { link: Simulations
      , title: "Simulation"
      , help: "Set up simulations to test your contract's behavior."
      }
    , { link: Transactions
      , title: "Transactions"
      , help: "See how your contract behaves on a simulated blockchain."
      }
    ]

  mkTab :: forall r. { link :: View, title :: String | r } -> HTML p HAction
  mkTab { link, title } =
    navItem_
      [ a
          [ id_ $ "tab-" <> String.toLower (show link)
          , classes $ [ navLink ] <> activeClass
          , onClick $ const $ Just $ ChangeView link
          ]
          [ text title ]
      ]
    where
    activeClass =
      if link == activeView then
        [ active ]
      else
        []

  helpText = case Array.find (\({ link }) -> link == activeView) tabs of
    Nothing -> Bootstrap.empty
    Just { help } -> text help
