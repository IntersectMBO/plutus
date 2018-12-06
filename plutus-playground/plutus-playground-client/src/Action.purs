module Action
       ( simulationPane
       ) where

import Bootstrap (badge, badgePrimary, btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSuccess, btnWarning, card, cardBody_, cardFooter_, col4_, col_, formControl, formGroup_, pullRight, row, row_)
import Control.Monad.Aff.Class (class MonadAff)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Int as Int
import Data.Lens (view)
import Data.Maybe (Maybe, fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.Tuple.Nested ((/\))
import Halogen (HTML)
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects)
import Halogen.HTML (ClassName(ClassName), br_, button, code_, div, div_, h2_, h3_, input, label, p_, small_, text)
import Halogen.HTML.Events (input_, onClick, onValueChange)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (InputType(InputText, InputNumber), class_, classes, disabled, for, placeholder, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(..))
import Playground.API (EvaluationResult, FunctionSchema, SimpleArgumentSchema)
import Prelude (const, map, show, ($), (+), (/=), (<$>), (<<<))
import Servant.PureScript.Affjax (AjaxError)
import Types (Action(Wait, Action), Blockchain, ChildQuery, ChildSlot, FormEvent(SetSubField, SetStringField, SetIntField), MockWallet, Query(EvaluateActions, AddWaitAction, PopulateAction, SetWaitTime, RemoveAction), SimpleArgument(Unknowable, SimpleObject, SimpleString, SimpleInt), _MockWallet, _wallet, validate)
import Wallet (walletIdPane, walletsPane)

simulationPane ::
  forall m aff.
  MonadAff (EChartsEffects aff) m
  => Array (FunctionSchema SimpleArgumentSchema)
  -> Array MockWallet
  -> Array Action
  -> RemoteData AjaxError EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
simulationPane schemas wallets actions evaluationResult =
  div_
    [ walletsPane schemas wallets
    , br_
    , actionsPane actions ((_.resultBlockchain <<< unwrap) <$> evaluationResult)
    ]

actionsPane :: forall p. Array Action -> RemoteData AjaxError Blockchain -> HTML p Query
actionsPane actions evaluationResult =
  div_
    [ h2_ [ text "Actions" ]
    , p_ [ text "This is your action sequence. Click 'Evaluate' to run these actions against a simulated blockchain." ]
    , div
        [ classes [ ClassName "actions", row ] ]
        (Array.cons addWaitActionPane (mapWithIndex actionPane actions))
    , br_
    , row_ [ evaluateActionsPane evaluationResult actions ]
    , br_
    , div_ [ small_ [ text "Run this set of actions against a simulated blockchain." ] ]
    ]

actionPane :: forall p. Int -> Action -> HTML p Query
actionPane index action =
  col4_
    [ div [ class_ $ ClassName "action" ]
      [ div [ class_ card ]
        [ cardBody_
          [ div
              [ classes [ badge, badgePrimary, ClassName "badge-action" ] ]
              [ text $ show (index + 1) ]
          , button
              [ classes [ btn, btnInfo, pullRight ]
              , onClick $ input_ $ RemoveAction index
              ]
              [ icon Close ]
          , case action of
              (Action {mockWallet, functionSchema}) ->
                div_
                  [ h3_
                      [ walletIdPane (view (_MockWallet <<< _wallet) mockWallet)
                      , text ": "
                      , text $ unwrap $ _.functionName $ unwrap functionSchema
                      ]
                  , actionArgumentForm index $ _.argumentSchema $ unwrap functionSchema
                  ]
              (Wait {blocks}) ->
                div_
                  [ h3_ [ text "Wait" ]
                  , row_
                      [ col_ [ text "Time" ]
                      , col_ [
                          input
                            [ type_ InputNumber
                            , value $ show blocks
                            , placeholder "Int"
                            , onValueChange $ map (HQ.action <<< SetWaitTime index) <<< Int.fromString
                            ]
                        ]
                      ]
                  ]
          ]
        , cardFooter_
           [ validationErrorsPane action
           ]
        ]
      ]
    ]

validationErrorsPane :: forall p i. Action -> HTML p i
validationErrorsPane action =
  div_ $ validationErrorPane <$> validate action
  where
    validationErrorPane err = div_ [ code_ [ text $ show err ] ]

validationClasses ::
  forall a r i.
  Maybe a
  -> Array ClassName
validationClasses =
  maybe [ ClassName "error" ] (const [])

actionArgumentForm :: forall p. Int -> Array SimpleArgument -> HTML p Query
actionArgumentForm index arguments =
  div_
    (Array.mapWithIndex
       (\i argument -> PopulateAction index i <$> actionArgumentField false argument)
       arguments)

actionArgumentField ::
  forall p. Warn "We're still not handling the Unknowable case."
  => Boolean
  -> SimpleArgument
  -> HTML p FormEvent
actionArgumentField _ (SimpleInt n) =
  input
    [ type_ InputNumber
    , classes $ Array.cons formControl $ validationClasses n
    , value $ maybe "" show n
    , placeholder "Int"
    , onValueChange $ map (HQ.action <<< SetIntField) <<< Int.fromString
    ]
actionArgumentField _ (SimpleString s) =
  input
    [ type_ InputText
    , classes $ Array.cons formControl $ validationClasses s
    , value $ fromMaybe "" s
    , placeholder "String"
    , onValueChange $ HE.input SetStringField
    ]
actionArgumentField indent (SimpleObject subFields) =
    (if indent
       then div [ classes [  ClassName "nested" ] ]
       else div_)
        (mapWithIndex (\i field -> map (SetSubField i) (subForm field)) subFields)
  where
    subForm (name /\ arg) =
      (formGroup_
         [ label [ for name ] [ text name ]
         , actionArgumentField true arg
         ]
      )
actionArgumentField _ Unknowable =
  div_ [ text "Unsupported."
       ]

addWaitActionPane :: forall p. HTML p Query
addWaitActionPane =
  col4_
    [ div
        [ class_ $ ClassName "add-wait-action" ]
        [ div [ class_ card
              , onClick $ input_ $ AddWaitAction 10
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
