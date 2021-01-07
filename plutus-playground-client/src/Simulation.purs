module Simulation
  ( simulationsPane
  , simulationsNav
  , simulatorTitle
  , actionsErrorPane
  ) where

import Types
import Bootstrap (active, alertDanger_, badge, badgePrimary, btn, btnDanger, btnDefault, btnGroup_, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, btnWarning, card, cardBody_, col, colFormLabel, col_, formControl, formGroup_, formRow_, nav, navItem, navLink, pullRight, responsiveThird, row, row_)
import Bootstrap as Bootstrap
import Cursor (Cursor, current)
import Cursor as Cursor
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Functor.Foldable (Fix)
import Data.Int as Int
import Data.Lens (preview, review, view)
import Data.Maybe (Maybe(..), isJust)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, IProp, a, br_, button, code_, div, div_, h1_, h2_, h3_, input, label, p_, pre_, small_, span, text, ul, li)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onClick, onDragEnd, onDragEnter, onDragLeave, onDragOver, onDragStart, onDrop, onValueInput)
import Halogen.HTML.Properties (InputType(..), class_, classes, disabled, draggable, for, id_, placeholder, required, type_, value)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(..))
import Language.Haskell.Interpreter as PI
import Ledger.Slot (Slot)
import Ledger.Value (Value)
import Network.RemoteData (RemoteData(Loading, NotAsked, Failure, Success))
import Playground.Lenses (_endpointDescription, _getEndpointDescription)
import Playground.Schema (actionArgumentForm)
import Playground.Types (ContractCall(..), EvaluationResult, PlaygroundError(..), Simulation(..), _CallEndpoint, _FunctionSchema)
import Prelude (const, map, pure, show, (#), ($), (+), (/=), (<$>), (<<<), (<>), (==), (>))
import Schema (FormArgumentF)
import Schema.Types (ActionEvent(..), FormArgument, SimulationAction(..), Signatures)
import Validation (_argument, validate)
import ValueEditor (valueForm)
import Wallet (walletIdPane, walletsPane)
import Wallet.Emulator.Wallet (Wallet)
import Web.Event.Event (Event)
import Web.HTML.Event.DragEvent (DragEvent)

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
  WebData (Either PlaygroundError EvaluationResult) ->
  ComponentHTML HAction ChildSlots m
simulationsPane initialValue actionDrag endpointSignatures simulations evaluationResult = case current simulations of
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
        [ class_ $ ClassName "simulations" ]
        [ simulationsNav simulations
        , div
            [ class_ $ ClassName "simulation" ]
            [ walletsPane endpointSignatures initialValue simulationWallets
            , actionsPane isValidWallet actionDrag simulationActions evaluationResult
            ]
        ]
  Nothing ->
    div_
      [ p_
          [ text "Return to the Editor and compile a contract to get started." ]
      ]

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
          [ span [ class_ $ ClassName "simulation-nav-item-text" ] [ text simulationName ]
          , if canClose then
              span
                [ onClick $ const $ Just $ RemoveSimulationSlot index
                , class_ $ ClassName "simulation-nav-item-control"
                ]
                [ icon Close ]
            else
              Bootstrap.empty
          ]
      ]
  ]
  where
  navLinkClasses = if activeIndex == index then [ navLink, active ] else [ navLink ]

addSimulationControl :: forall p. HTML p HAction
addSimulationControl =
  li
    [ id_ "simulation-nav-item-add"
    , class_ navItem
    ]
    [ a
        [ onClick $ const $ Just $ AddSimulationSlot
        , class_ navLink
        ]
        [ span
            [ class_ $ ClassName "simulation-nav-item-control" ]
            [ icon Plus ]
        ]
    ]

actionsPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Array (ContractCall FormArgument) -> WebData (Either PlaygroundError EvaluationResult) -> HTML p HAction
actionsPane isValidWallet actionDrag actions evaluationResult =
  div
    [ class_ $ ClassName "actions" ]
    [ h2_ [ text "Actions" ]
    , p_ [ text "This is your action sequence. Click 'Evaluate' to run these actions against a simulated blockchain." ]
    , Keyed.div
        [ classes $ [ row, ClassName "actions" ]
            <> if actionDrag == Nothing then
                []
              else
                [ ClassName "actions-being-dragged" ]
        ]
        ( Array.snoc
            (mapWithIndex (actionPane isValidWallet actionDrag) actions)
            (addWaitActionPane (Array.length actions))
        )
    , br_
    , row_ [ evaluateActionsPane evaluationResult actions ]
    , br_
    , div_ [ small_ [ text "Run this set of actions against a simulated blockchain." ] ]
    ]

actionPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Int -> ContractCall FormArgument -> Tuple String (HTML p HAction)
actionPane isValidWallet actionDrag index action =
  Tuple (show index)
    $ responsiveThird
        [ div
            ( [ classes
                  ( [ ClassName "action"
                    , ClassName ("action-" <> show index)
                    , ClassName
                        ( "action-"
                            <> ( case isValidWallet <$> (preview (_CallEndpoint <<< _caller) action) of
                                  Nothing -> "valid-wallet"
                                  Just true -> "valid-wallet"
                                  Just false -> "invalid-wallet"
                              )
                        )
                    ]
                      <> if actionDrag == Just index then
                          [ ClassName "drag-source" ]
                        else
                          []
                  )
              ]
                <> dragSourceProperties index
                <> dragTargetProperties index
            )
            [ div [ class_ card ]
                [ ChangeSimulation
                    <$> cardBody_
                        [ div
                            [ classes [ badge, badgePrimary, ClassName "badge-action" ] ]
                            [ text $ show (index + 1) ]
                        , button
                            [ classes [ btn, pullRight ]
                            , onClick $ const $ Just $ ModifyActions $ RemoveAction index
                            ]
                            [ icon Close ]
                        , actionPaneBody index action
                        ]
                ]
            ]
        ]

actionPaneBody :: forall p. Int -> ContractCall (Fix FormArgumentF) -> HTML p SimulationAction
actionPaneBody index (CallEndpoint { caller, argumentValues }) =
  div_
    [ h3_
        [ walletIdPane caller
        , text ": "
        , text $ view (_FunctionSchema <<< _endpointDescription <<< _getEndpointDescription) argumentValues
        ]
    , actionArgumentForm (PopulateAction index) $ view (_FunctionSchema <<< _argument) argumentValues
    ]

actionPaneBody index (PayToWallet { sender, recipient, amount }) =
  div_
    [ h3_ [ walletIdPane sender, text ": Pay To Wallet" ]
    , formGroup_
        [ label [ for "recipient" ] [ text "Recipient" ]
        , input
            [ type_ InputNumber
            , classes [ formControl ]
            , value $ show $ view _walletId recipient
            , required true
            , placeholder "Wallet ID"
            , onBigIntegerInput (ModifyActions <<< SetPayToWalletRecipient index <<< review _walletId)
            ]
        ]
    , formGroup_
        [ label [ for "amount" ] [ text "Amount" ]
        , valueForm (ModifyActions <<< SetPayToWalletValue index) amount
        ]
    ]

actionPaneBody index (AddBlocks { blocks }) =
  div_
    [ h3_ [ text "Wait" ]
    , waitTypeButtons index (Right blocks)
    , formGroup_
        [ formRow_
            [ label [ classes [ col, colFormLabel ] ]
                [ text "Blocks" ]
            , col_
                [ input
                    [ type_ InputNumber
                    , classes [ formControl, ClassName $ "action-argument-0-blocks" ]
                    , value $ show blocks
                    , placeholder "Block Number"
                    , onBigIntegerInput $ ModifyActions <<< SetWaitTime index
                    ]
                ]
            ]
        ]
    ]

actionPaneBody index (AddBlocksUntil { slot }) =
  div_
    [ h3_ [ text "Wait" ]
    , waitTypeButtons index (Left slot)
    , formGroup_
        [ formRow_
            [ label [ classes [ col, colFormLabel ] ]
                [ text "Slot" ]
            , col_
                [ input
                    [ type_ InputNumber
                    , classes [ formControl, ClassName $ "action-argument-0-until-slot" ]
                    , value $ show $ view _InSlot slot
                    , placeholder "Slot Number"
                    , onBigIntegerInput $ ModifyActions <<< SetWaitUntilTime index <<< review _InSlot
                    ]
                ]
            ]
        ]
    ]

waitTypeButtons :: forall p. Int -> Either Slot BigInteger -> HTML p SimulationAction
waitTypeButtons index wait =
  btnGroup_
    [ button
        ( case wait of
            Left slot -> [ classes inactiveClasses, onClick $ const $ Just $ ModifyActions $ SetWaitTime index $ view _InSlot slot ]
            Right _ -> [ classes activeClasses ]
        )
        [ text "Wait For…" ]
    , button
        ( case wait of
            Right blocks -> [ classes inactiveClasses, onClick $ const $ Just $ ModifyActions $ SetWaitUntilTime index $ review _InSlot blocks ]
            Left _ -> [ classes activeClasses ]
        )
        [ text "Wait Until…" ]
    ]
  where
  activeClasses = [ btn, btnSmall, btnInfo ]

  inactiveClasses = [ btn, btnSmall, btnDefault ]

validationClasses ::
  forall a.
  FormArgument ->
  Maybe a ->
  Array ClassName
validationClasses arg Nothing = [ ClassName "error" ]

validationClasses arg (Just _) = []

addWaitActionPane :: forall p. Int -> Tuple String (HTML p HAction)
addWaitActionPane index =
  Tuple "add-wait"
    $ responsiveThird
        [ div
            [ class_ $ ClassName "add-wait-action" ]
            [ div
                ( [ class_ card
                  , onClick $ const $ Just $ ChangeSimulation $ ModifyActions $ AddWaitAction $ BigInteger.fromInt 10
                  ]
                    <> dragTargetProperties index
                )
                [ cardBody_
                    [ icon Plus
                    , div_ [ text "Add Wait Action" ]
                    ]
                ]
            ]
        ]

evaluateActionsPane :: forall p. WebData (Either PlaygroundError EvaluationResult) -> Array (ContractCall FormArgument) -> HTML p HAction
evaluateActionsPane evaluationResult actions =
  col_
    [ button
        [ id_ "evaluate"
        , classes [ btn, btnClass evaluationResult hasErrors ]
        , disabled hasErrors
        , onClick $ const $ Just EvaluateActions
        ]
        [ btnText evaluationResult hasErrors ]
    ]
  where
  btnClass Loading _ = btnSecondary

  btnClass _ true = btnWarning

  btnClass (Success (Left _)) _ = btnDanger

  btnClass (Success _) _ = btnSuccess

  btnClass (Failure _) _ = btnDanger

  btnClass NotAsked _ = btnPrimary

  btnText Loading _ = icon Spinner

  btnText _ true = text "Fix Errors"

  btnText _ _ = text "Evaluate"

  validationErrors = Array.concat $ validate <$> actions

  hasErrors = validationErrors /= []

dragSourceProperties ::
  forall i.
  Int ->
  Array
    ( IProp
        ( draggable :: Boolean
        , onDragStart :: DragEvent
        , onDragEnd :: DragEvent
        | i
        )
        HAction
    )
dragSourceProperties index =
  [ draggable true
  , onDragStart $ dragAndDropAction index DragStart
  , onDragEnd $ dragAndDropAction index DragEnd
  ]

dragTargetProperties ::
  forall i.
  Int ->
  Array
    ( IProp
        ( onDragEnter :: DragEvent
        , onDragOver :: DragEvent
        , onDragLeave :: DragEvent
        , onDrop :: DragEvent
        | i
        )
        HAction
    )
dragTargetProperties index =
  [ onDragEnter $ dragAndDropAction index DragEnter
  , onDragOver $ dragAndDropAction index DragOver
  , onDragLeave $ dragAndDropAction index DragLeave
  , onDrop $ dragAndDropAction index Drop
  ]

dragAndDropAction :: Int -> DragAndDropEventType -> DragEvent -> Maybe HAction
dragAndDropAction index eventType = Just <<< ActionDragAndDrop index eventType

actionsErrorPane :: forall p i. PlaygroundError -> HTML p i
actionsErrorPane error =
  div
    [ class_ $ ClassName "ajax-error" ]
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

onBigIntegerInput :: forall i r. (BigInteger -> i) -> IProp ( onInput :: Event, value :: String | r ) i
onBigIntegerInput f = onValueInput $ map f <<< BigInteger.fromString
