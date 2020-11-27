module Action (actionsPane) where

import Types
import Bootstrap (active, alertDanger_, badge, badgePrimary, btn, btnDanger, btnDefault, btnGroup_, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, btnWarning, card, cardBody_, col, colFormLabel, col_, formControl, formGroup_, formRow_, nav, navItem, navLink, pullRight, responsiveThird, row, row_)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Lens (preview, review, view)
import Data.Maybe (Maybe(..), isJust)
import Data.Functor.Foldable (Fix)
import Data.String as String
import Data.Tuple (Tuple(..))
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, IProp, a, br_, button, code_, div, div_, h1_, h2_, h3_, input, label, p_, pre_, small_, span, text, ul, li)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onClick, onDragEnd, onDragEnter, onDragLeave, onDragOver, onDragStart, onDrop, onValueInput)
import Halogen.HTML.Properties (InputType(..), class_, classes, disabled, draggable, for, id_, placeholder, required, type_, value)
import Icons (Icon(..), icon)
import Ledger.Slot (Slot)
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
