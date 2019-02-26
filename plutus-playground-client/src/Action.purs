module Action
       ( simulationPane
       ) where

import Bootstrap (badge, badgePrimary, btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSuccess, btnWarning, card, cardBody_, col4_, col_, nbsp, formControl, formGroup_, invalidFeedback_, pullRight, row, row_, validFeedback_)
import Control.Monad.Aff.Class (class MonadAff)
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
import Halogen.HTML (ClassName(ClassName), br_, button, code_, div, div_, form, h2_, h3_, input, label, p_, small_, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (input_, onClick, onValueChange)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(InputText, InputNumber), class_, classes, disabled, for, placeholder, required, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(Loading, NotAsked, Failure, Success))
import Playground.API (EvaluationResult, SimulatorWallet, _EvaluationResult, _Fn, _FunctionSchema)
import Prelude (map, pure, show, ($), (+), (/=), (<$>), (<<<), (<>))
import Servant.PureScript.Affjax (AjaxError)
import Types (Action(..), ActionEvent(..), Blockchain, ChildQuery, ChildSlot, FormEvent(..), Query(..), SimpleArgument(..), Simulation, _argumentSchema, _functionName, _resultBlockchain, _simulatorWalletWallet)
import Validation (ValidationError, WithPath, addPath, validate)
import Wallet (walletIdPane, walletsPane)

simulationPane ::
  forall m aff.
  MonadAff (EChartsEffects aff) m
  => Simulation
  -> Array SimulatorWallet
  -> RemoteData AjaxError EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
simulationPane simulation wallets evaluationResult =
  div_
    [ walletsPane simulation.signatures wallets
    , br_
    , actionsPane simulation.actions (view (_EvaluationResult <<< _resultBlockchain) <$> evaluationResult)
    ]

actionsPane :: forall p. Array Action -> RemoteData AjaxError Blockchain -> HTML p Query
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
      [ div [ class_ $ ClassName "action" ]
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
                              , value $ show blocks
                              , placeholder "Int"
                              , onValueChange $ map (HQ.action <<< ModifyActions <<< SetWaitTime index) <<< Int.fromString
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

actionArgumentForm :: forall p. Int -> Array SimpleArgument -> HTML p Query
actionArgumentForm index arguments =
  form [ class_ $ ClassName "was-validated" ]
    (Array.mapWithIndex
       (\i argument -> PopulateAction index i <$> actionArgumentField ("Field " <> show i) false argument)
       arguments)

actionArgumentField ::
  forall p. Warn "We're still not handling the Unknowable case."
  => String
  -> Boolean
  -> SimpleArgument
  -> HTML p FormEvent
actionArgumentField context _ arg@(SimpleInt n) =
  div_ [
    input
      [ type_ InputNumber
      , class_ formControl
      , value $ maybe "" show n
      , required true
      , placeholder "Int"
      , onValueChange $ (Just <<< HQ.action <<< SetIntField <<< Int.fromString)
      ]
    , validationFeedback (addPath context <$> validate arg)
  ]
actionArgumentField context _ arg@(SimpleString s) =
  div_ [
    input
      [ type_ InputText
      , class_ formControl
      , value $ fromMaybe "" s
      , required true
      , placeholder "String"
      , onValueChange $ HE.input SetStringField
      ]
    , validationFeedback (addPath context <$> validate arg)
  ]
actionArgumentField context nested (SimpleTuple (subFieldA /\subFieldB)) =
  row_
    [ col_ [ SetSubField 1 <$> actionArgumentField "_1" true subFieldA ]
    , col_ [ SetSubField 2 <$> actionArgumentField "_2" true subFieldA ]
    ]
actionArgumentField context nested (SimpleArray schema subFields) =
    div_ [(if nested
           then div [ classes [  ClassName "nested" ] ]
           else div_) $ mapWithIndex (\i field -> map (SetSubField i) (subForm (show i) field)) subFields
         , button
             [ classes [ btn, btnInfo ]
             , onClick $ input_ AddSubField
             ]
             [ icon Plus ]
         ]
  where
    subForm name  arg =
      (formGroup_
         [ label [ for name ] [ text name ]
         , actionArgumentField name true arg
         ]
      )
actionArgumentField context nested (SimpleObject _ subFields) =
    (if nested
       then div [ classes [  ClassName "nested" ] ]
       else div_) $ mapWithIndex (\i field -> map (SetSubField i) (subForm field)) subFields
  where
    subForm (name /\ arg) =
      (formGroup_
         [ label [ for name ] [ text name ]
         , actionArgumentField name true arg
         ]
      )
actionArgumentField _ _ (Unknowable { context, description }) =
  div_ [ text $ "Unsupported: " <> context
       , code_ [ text description ]
       ]

validationFeedback :: forall p i. Array (WithPath ValidationError) -> HTML p i
validationFeedback [] =
  validFeedback_ [ nbsp ]
validationFeedback errors =
  invalidFeedback_ (div_ <<< pure <<< text <<< show <$> errors)

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

evaluateActionsPane :: forall p. RemoteData AjaxError Blockchain -> Array Action -> HTML p Query
evaluateActionsPane evaluationResult actions =
  col_
    [ button
      [ classes [ btn, btnClass evaluationResult hasErrors ]
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
