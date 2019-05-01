module Action
       ( simulationPane
       ) where

import Bootstrap (badge, badgePrimary, btn, btnDanger, btnGroup, btnGroupSmall, btnInfo, btnLink, btnPrimary, btnSecondary, btnSuccess, btnWarning, card, cardBody_, col10_, col2_, col_, formControl, formGroup_, invalidFeedback_, nbsp, pullRight, responsiveThird, row, row_, validFeedback_, wasValidated)
import Cursor (Cursor, current)
import Cursor as Cursor
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Int as Int
import Data.Lens (preview, view)
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.RawJson (JsonTuple(..))
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen (HTML)
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), IProp, br_, button, code_, div, div_, h2_, h3_, input, label, p_, small_, strong_, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick, onDragEnd, onDragEnter, onDragLeave, onDragOver, onDragStart, onDrop, onValueInput)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(InputText, InputNumber), class_, classes, disabled, draggable, for, id_, placeholder, required, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Ledger.Value (Value)
import Network.RemoteData (RemoteData(Loading, NotAsked, Failure, Success))
import Playground.API (EvaluationResult, _Fn, _FunctionSchema)
import Prelude (Unit, map, pure, show, (#), ($), (+), (/=), (<$>), (<<<), (<>), (==))
import Prim.TypeError (class Warn, Text)
import Types (Action(Wait, Action), ActionEvent(AddWaitAction, SetWaitTime, RemoveAction), Blockchain, ChildQuery, ChildSlot, DragAndDropEventType(..), FormEvent(..), Query(..), SimpleArgument(..), Simulation(Simulation), WebData, _Action, _argumentSchema, _functionName, _resultBlockchain, _simulatorWallet, _simulatorWalletWallet, _walletId)
import Validation (ValidationError, WithPath, joinPath, showPathValue, validate)
import ValueEditor (valueForm)
import Wallet (walletIdPane, walletsPane)
import Wallet.Emulator.Types (Wallet)
import Web.HTML.Event.DragEvent (DragEvent)

simulationPane ::
  forall m.
  Value
  -> Maybe Int
  -> Cursor Simulation
  -> WebData EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
simulationPane initialValue actionDrag simulations evaluationResult =
  case current simulations of
    Just (Simulation simulation) ->
      let
        isValidWallet :: Wallet -> Boolean
        isValidWallet target =
          isJust $ Array.find (\wallet -> view _walletId target
                                          ==
                                          view (_simulatorWalletWallet <<< _walletId) wallet)
                     simulation.wallets
      in
        div_
          [ simulationsNav simulations
          , walletsPane simulation.signatures initialValue simulation.wallets
          , br_
          , actionsPane isValidWallet actionDrag simulation.actions (view _resultBlockchain <$> evaluationResult)
          ]
    Nothing ->
      div_
        [ text "Click the "
        , strong_ [ text "Editor" ]
        , text " tab above and compile a contract to get started."
        ]

simulationsNav :: forall p . Cursor Simulation -> HTML p Query
simulationsNav simulations =
  div
    [ id_ "simulation-nav"
    , classes [ btnGroup, btnGroupSmall ]
    ]
    ((simulations
      # Cursor.mapWithIndex (simulationNavItem (Cursor.getIndex simulations))
      # Cursor.toArray
      # Array.concat
     )
     <>
     [ addSimulationControl ]
    )

simulationNavItem :: forall p. Int -> Int -> Simulation -> Array (HTML p Query)
simulationNavItem activeIndex index simulation =
  [ button
      [ id_ $ "simulation-nav-item-" <> show index
      , classes $ buttonClasses <> [ simulationNavItemNameClass ]
      , onClick $ input_ $ SetSimulationSlot index
      ]
      [ text $ "Simulation #" <> show (index + 1) ]
  , button
      [ id_ $ "simulation-nav-item-" <> show index <> "-remove"
      , classes $ buttonClasses <> [ simulationNavItemCloseClass ]
      , onClick $ input_ $ RemoveSimulationSlot index
      ]
      [ icon Close ]
  ]
  where
    buttonClasses =
        [ btn, simulationNavItemClass ]
        <>
        if activeIndex == index then [ btnPrimary ] else [ btnInfo ]

simulationNavItemClass :: ClassName
simulationNavItemClass = ClassName "simulation-nav-item"

simulationNavItemNameClass :: ClassName
simulationNavItemNameClass = ClassName "simulation-nav-item-name"

simulationNavItemCloseClass :: ClassName
simulationNavItemCloseClass = ClassName "simulation-nav-item-close"

addSimulationControl :: forall p. HTML p Query
addSimulationControl =
  button
    [ id_ "simulation-nav-item-add"
    , classes [ btn, btnInfo, simulationNavItemClass ]
    , onClick $ input_ $ AddSimulationSlot
    ]
    [ icon Plus ]

actionsPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Array Action -> WebData Blockchain -> HTML p Query
actionsPane isValidWallet actionDrag actions evaluationResult =
  div_
    [ h2_ [ text "Actions" ]
    , p_ [ text "This is your action sequence. Click 'Evaluate' to run these actions against a simulated blockchain." ]
    , Keyed.div
        [ classes $ [ row, ClassName "actions" ]
                    <>
                    if actionDrag == Nothing
                    then []
                    else [ ClassName "actions-being-dragged" ]
        ]
        (Array.snoc
           (mapWithIndex (actionPane isValidWallet actionDrag) actions)
           (addWaitActionPane (Array.length actions)))
    , br_
    , row_ [ evaluateActionsPane evaluationResult actions ]
    , br_
    , div_ [ small_ [ text "Run this set of actions against a simulated blockchain." ] ]
    ]

actionPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Int -> Action -> Tuple String (HTML p Query)
actionPane isValidWallet actionDrag index action =
  Tuple (show index) $
    responsiveThird
      [ div ([ classes ([ ClassName "action"
                        , ClassName ("action-" <> show index)
                        , ClassName ("action-" <> (case isValidWallet <$> (preview (_Action <<< _simulatorWallet <<< _simulatorWalletWallet) action) of
                                                      Nothing -> "valid-wallet"
                                                      Just true ->  "valid-wallet"
                                                      Just false ->  "invalid-wallet"))
                        ]
                        <> if actionDrag == Just index
                           then [ ClassName "drag-source" ]
                           else []
                       )
             ]
             <> dragSourceProperties index
             <> dragTargetProperties index
            )
        [ div [ class_ card ]
          [ cardBody_
            [ div
                [ classes [ badge, badgePrimary, ClassName "badge-action" ] ]
                [ text $ show (index + 1) ]
            , button
                [ classes [ btn, btnInfo, pullRight ]
                , onClick $ input_ $ ModifyActions $ RemoveAction index
                ]
                [ icon Close ]
            , case action of
                Action {simulatorWallet, functionSchema} ->
                  div_
                    [ h3_
                        [ walletIdPane (view _simulatorWalletWallet simulatorWallet)
                        , text ": "
                        , text $ view (_FunctionSchema <<< _functionName <<< _Fn) functionSchema
                        ]
                    , actionArgumentForm index $ view (_FunctionSchema <<< _argumentSchema) functionSchema
                    ]
                Wait {blocks} ->
                  div_
                    [ h3_ [ text "Wait" ]
                    , row_
                        [ col_ [ text "Time" ]
                        , col_ [
                            input
                              [ type_ InputNumber
                              , classes [ formControl, ClassName $ "action-argument-0-blocks" ]
                              , value $ show blocks
                              , placeholder "Int"
                              , onValueInput $ map (HQ.action <<< ModifyActions <<< SetWaitTime index) <<< Int.fromString
                              ]
                          ]
                        ]
                    ]
            ]
          ]
        ]
      ]

validationClasses ::
  forall a.
  SimpleArgument
  -> Maybe a
  -> Array ClassName
validationClasses arg Nothing = [ ClassName "error" ]
validationClasses arg (Just _) = []

actionArgumentClass :: Array String -> Array ClassName
actionArgumentClass ancestors =
  [ ClassName "action-argument"
  , ClassName $ "action-argument-" <> Array.intercalate "-" ancestors
  ]

actionArgumentForm :: forall p. Int -> Array SimpleArgument -> HTML p Query
actionArgumentForm index arguments =
  div [ class_ wasValidated ]
    (Array.mapWithIndex
       (\i argument -> PopulateAction index i <$> actionArgumentField [ show i ] false argument)
       arguments)

actionArgumentField ::
  forall p. Warn (Text "We're still not handling the Unknowable case.")
  => Array String
  -> Boolean
  -> SimpleArgument
  -> HTML p FormEvent
actionArgumentField ancestors _ arg@(SimpleInt n) =
  div_ [
    input
      [ type_ InputNumber
      , classes (Array.cons formControl (actionArgumentClass ancestors))
      , value $ maybe "" show n
      , required true
      , placeholder "Int"
      , onValueInput $ (Just <<< HQ.action <<< SetIntField <<< Int.fromString)
      ]
    , validationFeedback (joinPath ancestors <$> validate arg)
  ]
actionArgumentField ancestors _ arg@(SimpleString s) =
  div_ [
    input
      [ type_ InputText
      , classes (Array.cons formControl (actionArgumentClass ancestors))
      , value $ fromMaybe "" s
      , required true
      , placeholder "String"
      , onValueInput $ HE.input SetStringField
      ]
    , validationFeedback (joinPath ancestors <$> validate arg)
  ]
actionArgumentField ancestors _ arg@(SimpleHex s) =
  div_ [
    input
      [ type_ InputText
      , classes (Array.cons formControl (actionArgumentClass ancestors))
      , value $ fromMaybe "" s
      , required true
      , placeholder "String"
      , onValueInput $ HE.input SetHexField
      ]
    , validationFeedback (joinPath ancestors <$> validate arg)
  ]
actionArgumentField ancestors isNested (SimpleTuple (JsonTuple (Tuple subFieldA subFieldB))) =
  row_
    [ col_ [ SetSubField 1 <$> actionArgumentField (Array.snoc ancestors "_1") true subFieldA ]
    , col_ [ SetSubField 2 <$> actionArgumentField (Array.snoc ancestors "_2") true subFieldB ]
    ]
actionArgumentField ancestors isNested (SimpleArray schema subFields) =
    div_ [ Keyed.div [ nesting isNested ]
             (mapWithIndex subFormContainer subFields)
         , button
             [ classes [ btn, btnInfo ]
             , onClick $ input_ AddSubField
             ]
             [ icon Plus ]
         ]
  where
    subFormContainer i field =
      show i
      /\
      formGroup_ [
        row_
          [ col10_
              [ SetSubField i <$> actionArgumentField (Array.snoc ancestors (show i)) true field ]
          , col2_
            [ button
              [ classes [ btn, btnLink ]
              , onClick $ input_ (RemoveSubField i)
              ]
              [ icon Trash ]
            ]
          ]
        ]

actionArgumentField ancestors isNested (SimpleObject _ subFields) =
  div [ nesting isNested ]
    (mapWithIndex (\i (JsonTuple field) -> map (SetSubField i) (subForm field)) subFields)
  where
    subForm (name /\ arg) =
      (formGroup_
         [ label [ for name ] [ text name ]
         , actionArgumentField (Array.snoc ancestors name) true arg
         ]
      )
actionArgumentField ancestors isNested (ValueArgument _ value) =
  div [ nesting isNested ]
    [ label [ for "value" ] [ text "Value" ]
    , valueForm SetValueField value
    ]
actionArgumentField _ _ (Unknowable { context, description }) =
  div_ [ text $ "Unsupported: " <>  context
       , code_ [ text description ]
       ]

nesting :: forall r i. Boolean -> IProp ("class" :: String | r) i
nesting true = classes [ ClassName "nested" ]
nesting false = classes []

validationFeedback :: forall p i. Array (WithPath ValidationError) -> HTML p i
validationFeedback [] =
  validFeedback_ [ nbsp ]
validationFeedback errors =
  invalidFeedback_ (div_ <<< pure <<< text <<< showPathValue <$> errors)

addWaitActionPane :: forall p. Int -> Tuple String (HTML p Query)
addWaitActionPane index =
  Tuple "add-wait" $
    responsiveThird
      [ div
          [ class_ $ ClassName "add-wait-action" ]
          [ div ([ class_ card
                , onClick $ input_ $ ModifyActions $ AddWaitAction 10
                ]
                 <> dragTargetProperties index)
              [ cardBody_
                  [ icon Plus
                  , div_ [ text "Add Wait Action" ]
                  ]
              ]
          ]
      ]

evaluateActionsPane :: forall p. WebData Blockchain -> Array Action -> HTML p Query
evaluateActionsPane evaluationResult actions =
  col_
    [ button
      [ id_ "evaluate"
      , classes [ btn, btnClass evaluationResult hasErrors ]
      , disabled hasErrors
      , onClick $ input_ EvaluateActions
      ]
      [ btnText evaluationResult hasErrors ]
    ]
  where
    btnClass Loading _ = btnSecondary
    btnClass _ true = btnWarning
    btnClass (Success _) _ = btnSuccess
    btnClass (Failure _) _ = btnDanger
    btnClass NotAsked _ = btnPrimary

    btnText Loading _ = icon Spinner
    btnText _ true = text "Fix Errors"
    btnText _ _ = text "Evaluate"

    validationErrors = Array.concat $ validate <$> actions

    hasErrors = validationErrors /= []

dragSourceProperties :: forall i.
  Int
  -> Array
       (IProp
          ( draggable :: Boolean
          , onDragStart :: DragEvent
          , onDragEnd :: DragEvent
          | i
          )
          (Query Unit)
       )
dragSourceProperties index =
  [ draggable true
  , onDragStart $ dragAndDropAction index DragStart
  , onDragEnd $ dragAndDropAction index DragEnd
  ]

dragTargetProperties ::
  forall i.
  Int
  -> Array
       (IProp
          ( onDragEnter :: DragEvent
          , onDragOver :: DragEvent
          , onDragLeave :: DragEvent
          , onDrop :: DragEvent
          | i
          )
          (Query Unit)
       )
dragTargetProperties index =
  [ onDragEnter $ dragAndDropAction index DragEnter
  , onDragOver $ dragAndDropAction index DragOver
  , onDragLeave $ dragAndDropAction index DragLeave
  , onDrop $ dragAndDropAction index Drop
  ]

dragAndDropAction :: Int -> DragAndDropEventType -> DragEvent -> Maybe (Query Unit)
dragAndDropAction index eventType =
  Just <<< HQ.action <<< ActionDragAndDrop index eventType
