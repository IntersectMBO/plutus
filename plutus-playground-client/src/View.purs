module View (render) where

import Types
import Action (actionsErrorPane, simulationPane)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (active, alert, alertPrimary, btn, btnGroup, btnSmall, colSm5, colSm6, colXs12, container, container_, empty, floatRight, hidden, justifyContentBetween, navItem_, navLink, navTabs_, noGutters, row)
import Chain (evaluationPane)
import Control.Monad.State (evalState)
import Data.Either (Either(..))
import Data.Json.JsonEither (JsonEither(..))
import Data.Lens (view)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.String as String
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Editor (demoScriptsPane, editorPane)
import Effect.Aff.Class (class MonadAff)
import Gists (gistControls)
import Halogen.HTML (ClassName(ClassName), HTML, ComponentHTML, a, div, div_, h1, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, href, id_)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(..))
import Prelude (const, show, ($), (<$>), (<>), (==))
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State -> ComponentHTML HAction ChildSlots m
render state@(State { currentView, blockchainVisualisationState }) =
  div_
    [ bannerMessage
    , div
        [ class_ $ ClassName "main-frame" ]
        [ container_
            [ mainHeader
            , div [ classes [ row, noGutters, justifyContentBetween ] ]
                [ div [ classes [ colXs12, colSm6 ] ] [ mainTabBar currentView ]
                , div [ classes [ colXs12, colSm5 ] ] [ gistControls (unwrap state) ]
                ]
            ]
        , viewContainer currentView Editor
            [ demoScriptsPane
            , editorPane defaultContents (unwrap <$> view _compilationResult state)
            , case view _compilationResult state of
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
  defaultContents = Map.lookup "Vesting" StaticData.demoFiles

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
mainTabBar activeView = navTabs_ (mkTab <$> tabs)
  where
  tabs =
    [ Editor /\ "Editor"
    , Simulations /\ "Simulation"
    , Transactions /\ "Transactions"
    ]

  mkTab :: Tuple View String -> HTML p HAction
  mkTab (link /\ title) =
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
