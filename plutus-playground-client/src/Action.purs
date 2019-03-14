module Action
       ( simulationPane
       ) where

import Bootstrap (badge, badgePrimary, btn, btnDanger, btnGroup, btnGroupSmall, btnInfo, btnLink, btnPrimary, btnSecondary, btnSuccess, btnWarning, card, cardBody_, col10_, col2_, col4_, col_, formControl, formGroup_, invalidFeedback_, nbsp, pullRight, row, row_, validFeedback_)
import Control.Monad.Aff.Class (class MonadAff)
import Cursor (Cursor, current)
import Cursor as Cursor
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Int as Int
import Data.Lens (view)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen (HTML)
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.HTML (ClassName(ClassName), br_, button, code_, div, div_, form, h2_, h3_, input, label, p_, small_, strong_, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick, onValueInput)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(InputText, InputNumber), class_, classes, disabled, for, id_, placeholder, required, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(Loading, NotAsked, Failure, Success))
import Playground.API (EvaluationResult, _Fn, _FunctionSchema)
import Prelude (map, pure, show, (#), ($), (+), (/=), (<$>), (<<<), (<>), (==))
import Types (Action(Wait, Action), ActionEvent(AddWaitAction, SetWaitTime, RemoveAction), Blockchain, ChildQuery, ChildSlot, FormEvent(SetSubField, AddSubField, RemoveSubField, SetStringField, SetIntField), Query(..), SimpleArgument(Unknowable, SimpleObject, SimpleArray, SimpleTuple, SimpleString, SimpleInt), Simulation(Simulation), WebData, _argumentSchema, _functionName, _resultBlockchain, _simulatorWalletWallet)
import Validation (ValidationError, WithPath, joinPath, showPathValue, validate)
import Wallet (walletIdPane, walletsPane)

simulationPane ::
  forall m aff.
  MonadAff (EChartsEffects aff) m
  => Cursor Simulation
  -> WebData EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
simulationPane simulations evaluationResult =
  case current simulations of
    Just (Simulation simulation) ->
      div_
        [ simulationsNav simulations
        , walletsPane simulation.signatures simulation.wallets
        , br_
        , actionsPane simulation.actions (view _resultBlockchain <$> evaluationResult)
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
      , buttonClasses
      , onClick $ input_ $ SetSimulationSlot index
      ]
      [ text $ "Simulation #" <> show (index + 1) ]
  , button
      [ id_ $ "simulation-nav-item-" <> show index <> "-remove"
      , buttonClasses
      , onClick $ input_ $ RemoveSimulationSlot index
      ]
      [ icon Close ]
  ]
  where
    buttonClasses =
      classes ([ btn, simulationNavItemClass ] <> if activeIndex == index then [ btnPrimary ] else [ btnInfo ])

simulationNavItemClass :: ClassName
simulationNavItemClass = ClassName "simulation-nav-item"

addSimulationControl :: forall p. HTML p Query
addSimulationControl =
  button
    [ id_ "simulation-nav-item-add"
    , classes [ btn, btnInfo, simulationNavItemClass ]
    , onClick $ input_ $ AddSimulationSlot
    ]
    [ icon Plus ]

actionsPane :: forall p. Array Action -> WebData Blockchain -> HTML p Query
actionsPane actions evaluationResult =
  div_
    [ h2_ [ text "Actions" ]
    , p_ [ text "This is your action sequence. Click 'Evaluate' to run these actions against a simulated blockchain." ]
    , Keyed.div
        [ classes [ ClassName "actions", row ] ]
        (Array.snoc (mapWithIndex actionPane actions) addWaitActionPane)
    , br_
    , row_ [ evaluateActionsPane evaluationResult actions ]
    , br_
    , div_ [ small_ [ text "Run this set of actions against a simulated blockchain." ] ]
    ]

actionPane :: forall p. Int -> Action -> Tuple String (HTML p Query)
actionPane index action =
  Tuple (show index) $
    col4_
      [ div [ classes [ ClassName "action", ClassName ("action-" <> show index) ] ]
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
  form [ class_ $ ClassName "was-validated" ]
    (Array.mapWithIndex
       (\i argument -> PopulateAction index i <$> actionArgumentField [ show i ] false argument)
       arguments)

actionArgumentField ::
  forall p. Warn "We're still not handling the Unknowable case."
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
actionArgumentField ancestors nested (SimpleTuple (subFieldA /\subFieldB)) =
  row_
    [ col_ [ SetSubField 1 <$> actionArgumentField (Array.snoc ancestors "_1") true subFieldA ]
    , col_ [ SetSubField 2 <$> actionArgumentField (Array.snoc ancestors "_2") true subFieldB ]
    ]
actionArgumentField ancestors nested (SimpleArray schema subFields) =
    div_ [(if nested
           then Keyed.div [ classes [  ClassName "nested" ] ]
           else Keyed.div_) (mapWithIndex subFormContainer subFields)
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

actionArgumentField ancestors nested (SimpleObject _ subFields) =
    (if nested
       then div [ classes [  ClassName "nested" ] ]
       else div_) $ mapWithIndex (\i field -> map (SetSubField i) (subForm field)) subFields
  where
    subForm (name /\ arg) =
      (formGroup_
         [ label [ for name ] [ text name ]
         , actionArgumentField (Array.snoc ancestors name) true arg
         ]
      )
actionArgumentField _ _ (Unknowable { context, description }) =
  div_ [ text $ "Unsupported: " <>  context
       , code_ [ text description ]
       ]

validationFeedback :: forall p i. Array (WithPath ValidationError) -> HTML p i
validationFeedback [] =
  validFeedback_ [ nbsp ]
validationFeedback errors =
  invalidFeedback_ (div_ <<< pure <<< text <<< showPathValue <$> errors)

addWaitActionPane :: forall p. Tuple String (HTML p Query)
addWaitActionPane =
  Tuple "add-wait" $
    col4_
      [ div
          [ class_ $ ClassName "add-wait-action" ]
          [ div [ class_ card
                , onClick $ input_ $ ModifyActions $ AddWaitAction 10
                ]
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
