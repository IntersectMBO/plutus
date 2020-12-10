module Action (actionsPane) where

import Types
import Bootstrap (btn, card, cardBody_, col, colFormLabel, col_, formCheck, formCheckInline, formCheckInput, formCheckLabel, formControl, formGroup_, formRow_, floatRight)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Lens (preview, review, view)
import Data.Maybe (Maybe(..))
import Data.Functor.Foldable (Fix)
import Data.Tuple (Tuple(..))
import Halogen.HTML (ClassName(ClassName), HTML, IProp, button, div, div_, h2_, h3_, input, label, p_, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onChange, onClick, onDragEnd, onDragEnter, onDragLeave, onDragOver, onDragStart, onDrop, onValueInput)
import Halogen.HTML.Properties (InputType(..), checked, class_, classes, draggable, for, id_, name, placeholder, required, type_, value)
import Icons (Icon(..), icon)
import Ledger.Slot (Slot)
import Playground.Lenses (_endpointDescription, _getEndpointDescription)
import Playground.Schema (actionArgumentForm)
import Playground.Types (ContractCall(..), EvaluationResult, PlaygroundError, _CallEndpoint, _FunctionSchema)
import Prelude (const, map, show, ($), (+), (<$>), (<<<), (<>), (==))
import Schema (FormArgumentF)
import Schema.Types (ActionEvent(..), FormArgument, SimulationAction(..))
import Validation (_argument)
import ValueEditor (valueForm)
import Wallet (walletIdPane)
import Wallet.Emulator.Wallet (Wallet)
import Web.Event.Event (Event)
import Web.HTML.Event.DragEvent (DragEvent)

actionClass :: ClassName
actionClass = ClassName "action"

actionsPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Array (ContractCall FormArgument) -> WebData (Either PlaygroundError EvaluationResult) -> HTML p HAction
actionsPane isValidWallet actionDrag actions evaluationResult =
  div
    [ class_ $ ClassName "actions" ]
    [ h2_ [ text "Actions" ]
    , p_ [ text "This is your action sequence. Click 'Evaluate' to run these actions against a simulated blockchain." ]
    , Keyed.div
        [ classes $ [ ClassName "action-list" ]
            <> if actionDrag == Nothing then
                []
              else
                [ ClassName "actions-being-dragged" ]
        ]
        ( Array.snoc
            (mapWithIndex (actionPane isValidWallet actionDrag) actions)
            (addWaitActionPane (Array.length actions))
        )
    ]

actionPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Int -> ContractCall FormArgument -> Tuple String (HTML p HAction)
actionPane isValidWallet actionDrag index action =
  Tuple (show index)
    $ div
        ( [ classes
              ( [ card
                , actionClass
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
        [ ChangeSimulation
            <$> cardBody_
                [ div
                    [ class_ $ ClassName "action-label" ]
                    [ text $ show (index + 1) ]
                , button
                    [ classes [ btn, floatRight, ClassName "close-button" ]
                    , onClick $ const $ Just $ ModifyActions $ RemoveAction index
                    ]
                    [ icon Close ]
                , actionPaneBody index action
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
  div
    [ class_ $ ClassName "wait-type-options" ]
    [ div
        [ classes [ formCheck, formCheckInline ] ]
        [ input
            ( case wait of
                Left slot -> baseInputProps <> [ id_ waitForId, onChange $ const $ Just $ ModifyActions $ SetWaitTime index $ view _InSlot slot ]
                Right _ -> baseInputProps <> [ id_ waitForId, checked true ]
            )
        , label
            [ class_ formCheckLabel
            , for waitForId
            ]
            [ text "Wait For…" ]
        ]
    , div
        [ classes [ formCheck, formCheckInline ] ]
        [ input
            ( case wait of
                Right blocks -> baseInputProps <> [ id_ waitUntilId, onChange $ const $ Just $ ModifyActions $ SetWaitUntilTime index $ review _InSlot blocks ]
                Left _ -> baseInputProps <> [ id_ waitForId, checked true ]
            )
        , label
            [ class_ formCheckLabel
            , for waitUntilId
            ]
            [ text "Wait Until…" ]
        ]
    ]
  where
  baseInputProps = [ type_ InputRadio, class_ formCheckInput, name $ "wait-" <> show index ]

  waitForId = "wait-for-" <> show index

  waitUntilId = "wait-until-" <> show index

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
    $ div
        [ classes [ actionClass, ClassName "add-wait-action" ] ]
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

onBigIntegerInput :: forall i r. (BigInteger -> i) -> IProp ( onInput :: Event, value :: String | r ) i
onBigIntegerInput f = onValueInput $ map f <<< BigInteger.fromString
