module Simulation
  ( simulationsPaneRefLabel
  , simulationsErrorRefLabel
  , simulationsPane
  , simulationsNav
  , simulatorTitle
  ) where

import Types
import Action (actionsPane)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (active, alertDanger_, btn, btnDanger, btnWarning, empty, floatRight, nav, navItem, navLink)
import Cursor (Cursor, current)
import Cursor as Cursor
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust)
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen (RefLabel(RefLabel))
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, IProp, a, button, code_, div, div_, h1_, p_, pre_, span, text, ul, li)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, id_, ref)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(..))
import Language.Haskell.Interpreter as PI
import Ledger.Value (Value)
import Network.RemoteData (RemoteData(Loading, Failure, Success))
import Playground.Types (ContractCall, EvaluationResult, PlaygroundError(..), Simulation(..))
import Prelude (const, map, pure, show, (#), ($), (/=), (<$>), (<<<), (<>), (==), (>))
import Schema.Types (FormArgument, Signatures)
import Validation (validate)
import Wallet (walletsPane)
import Wallet.Emulator.Wallet (Wallet)
import Web.Event.Event (Event)

-- halogen reflabels for elements that need to be scolled into view
simulationsPaneRefLabel :: RefLabel
simulationsPaneRefLabel = RefLabel "simulations-pane"

simulationsErrorRefLabel :: RefLabel
simulationsErrorRefLabel = RefLabel "simulation-errors"

-- repeated class names
navItemButtonClass :: ClassName
navItemButtonClass = ClassName "simulation-nav-item-control"

-- renders the simulator view title
simulatorTitle ::
  forall m.
  MonadAff m =>
  ComponentHTML HAction ChildSlots m
simulatorTitle =
  div
    [ class_ $ ClassName "main-header" ]
    [ h1_ [ text "Simulator" ]
    , a
        [ class_ btn
        , onClick $ const $ Just $ ChangeView Editor
        ]
        [ text "< Return to Editor" ]
    ]

-- renders the simulations pane
simulationsPane ::
  forall m.
  Value ->
  Maybe Int ->
  Signatures ->
  Cursor Simulation ->
  Maybe Simulation ->
  WebData (Either PlaygroundError EvaluationResult) ->
  ComponentHTML HAction ChildSlots m
simulationsPane initialValue actionDrag endpointSignatures simulations lastEvaluatedSimulation evaluationResult = case current simulations of
  Just (Simulation simulation@{ simulationWallets, simulationActions }) ->
    let
      isValidWallet :: Wallet -> Boolean
      isValidWallet target =
        isJust
          $ Array.find
              ( \wallet ->
                  view _walletId target
                    == view (_simulatorWalletWallet <<< _walletId) wallet
              )
              simulationWallets
    in
      div
        [ class_ $ ClassName "simulations"
        , ref simulationsPaneRefLabel
        ]
        [ simulationsNav simulations
        , div
            [ class_ $ ClassName "simulation" ]
            [ div
                [ classes [ ClassName "simulation-controls", floatRight ] ]
                [ evaluateActionsButton evaluationResult simulationActions
                , viewTransactionsButton simulations lastEvaluatedSimulation evaluationResult
                ]
            , walletsPane endpointSignatures initialValue simulationWallets
            , actionsPane isValidWallet actionDrag simulationActions evaluationResult
            , div
                [ classes [ ClassName "simulation-controls" ] ]
                [ evaluateActionsButton evaluationResult simulationActions
                , viewTransactionsButton simulations lastEvaluatedSimulation evaluationResult
                ]
            , case evaluationResult of
                Failure error -> ajaxErrorPane error
                Success (Left error) -> actionsErrorPane error
                _ -> empty
            ]
        ]
  Nothing ->
    div_
      [ p_
          [ text "Return to the Editor and compile a contract to get started." ]
      ]

-- renders the simulations tab interface
simulationsNav :: forall p. Cursor Simulation -> HTML p HAction
simulationsNav simulations =
  ul
    [ classes [ nav, ClassName "nav-tabs" ]
    ]
    ( ( simulations
          # Cursor.mapWithIndex (simulationNavItem (Cursor.length simulations > 1) (Cursor.getIndex simulations))
          # Cursor.toArray
          # Array.concat
      )
        <> [ addSimulationControl ]
    )

-- renders a simulation tab
simulationNavItem :: forall p. Boolean -> Int -> Int -> Simulation -> Array (HTML p HAction)
simulationNavItem canClose activeIndex index (Simulation { simulationName }) =
  [ li
      [ id_ $ "simulation-nav-item-" <> show index
      , class_ navItem
      ]
      [ a
          [ classes navLinkClasses
          , onClick $ const $ Just $ SetSimulationSlot index
          ]
          [ text simulationName ]
      , if canClose then
          button
            [ classes [ btn, navItemButtonClass ]
            , onClick $ const $ Just $ RemoveSimulationSlot index
            ]
            [ icon Close ]
        else
          empty
      ]
  ]
  where
  navLinkClasses = if activeIndex == index then [ navLink, active ] else [ navLink ]

-- renders the add simulation control (at the end of the tabs)
addSimulationControl :: forall p. HTML p HAction
addSimulationControl =
  li
    [ id_ "simulation-nav-item-add"
    , class_ navItem
    ]
    [ span
        [ class_ navLink ]
        [ button
            [ classes [ btn, navItemButtonClass ]
            , onClick $ const $ Just $ AddSimulationSlot
            ]
            [ icon Plus ]
        ]
    ]

-- renders the button for evaluating actions (running the simulation)
evaluateActionsButton :: forall p. WebData (Either PlaygroundError EvaluationResult) -> Array (ContractCall FormArgument) -> HTML p HAction
evaluateActionsButton evaluationResult actions =
  button
    [ classes [ btn, btnClass evaluationResult hasErrors ]
    , disabled hasErrors
    , onClick $ const $ Just EvaluateActions
    ]
    [ btnText evaluationResult hasErrors ]
  where
  btnClass _ true = btnWarning

  btnClass (Success (Left _)) _ = btnDanger

  btnClass (Failure _) _ = btnDanger

  btnClass _ _ = ClassName "btn-green"

  btnText Loading _ = icon Spinner

  btnText _ true = text "Fix Errors"

  btnText _ _ = text "Evaluate"

  validationErrors = Array.concat $ validate <$> actions

  hasErrors = validationErrors /= []

-- renders the button for viewing transactions (the results of the simulation)
viewTransactionsButton :: forall p. Cursor Simulation -> Maybe Simulation -> WebData (Either PlaygroundError EvaluationResult) -> HTML p HAction
viewTransactionsButton simulations lastEvaluatedSimulation evaluationResult =
  button
    [ classes [ btn, ClassName "btn-turquoise" ]
    , disabled isDisabled
    , onClick $ const $ Just $ ChangeView Transactions
    ]
    [ text "Transactions" ]
  where
  isDisabled = case evaluationResult of
    Success _ -> (current simulations) /= lastEvaluatedSimulation
    _ -> true

-- renders the evaluations error pane
actionsErrorPane :: forall p i. PlaygroundError -> HTML p i
actionsErrorPane error =
  div
    [ class_ $ ClassName "ajax-error"
    , ref simulationsErrorRefLabel
    ]
    [ alertDanger_
        ( (div_ <<< pure)
            <$> (showPlaygroundError error <> [ text "Please try again or contact support for assistance." ])
        )
    ]

-- | There's a few errors that make sense to display nicely, others should not occur so lets
-- | not deal with them.
showPlaygroundError :: forall p i. PlaygroundError -> Array (HTML p i)
showPlaygroundError (CompilationErrors errors) =
  [ text "Compilation Errors" ]
    <> (showCompilationError <$> errors)

showPlaygroundError (InterpreterError (PI.TimeoutError error)) =
  [ text "Interpreter Timed Out"
  , code_ [ text error ]
  ]

showPlaygroundError (InterpreterError (PI.CompilationErrors errors)) =
  [ text "Interpreter Errors" ]
    <> (showCompilationError <$> errors)

showPlaygroundError (RollupError error) =
  [ text "Error Calculating Final Blockchain State"
  , code_ [ text error ]
  ]

showPlaygroundError (OtherError error) =
  [ text "Unknown Evaluation Error"
  , code_ [ text error ]
  ]

showPlaygroundError (JsonDecodingError { expected, decodingError, input }) =
  [ text "Decoding Error"
  , code_ [ text $ "Expected: " <> expected ]
  , code_ [ text $ "Error: " <> decodingError ]
  , code_ [ text $ "Input: " <> input ]
  ]

showCompilationError :: forall p i. CompilationError -> HTML p i
showCompilationError (RawError error) = code_ [ text error ]

showCompilationError (CompilationError { text: errors }) = pre_ [ text (String.joinWith "\n" errors) ]

onIntInput :: forall i r. (Int -> i) -> IProp ( onInput :: Event, value :: String | r ) i
onIntInput f = onValueInput $ map f <<< Int.fromString
