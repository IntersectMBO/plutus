module Action
  ( simulationPane
  , actionsErrorPane
  ) where

import Types
import Bootstrap (alertDanger_, badge, badgePrimary, btn, btnDanger, btnGroup, btnGroupSmall, btnGroup_, btnInfo, btnLink, btnPrimary, btnSecondary, btnSmall, btnSuccess, btnWarning, card, cardBody_, col, col10_, col2_, colFormLabel, col_, formCheckInput, formCheckLabel, formCheck_, formControl, formGroup, formGroup_, formRow_, formText, inputGroupAppend_, inputGroupPrepend_, inputGroup_, invalidFeedback_, nbsp, pullRight, responsiveThird, row, row_, textMuted, validFeedback_, wasValidated)
import Bootstrap as Bootstrap
import Cursor (Cursor, current)
import Cursor as Cursor
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Functor.Foldable (Fix(..))
import Data.Int as Int
import Data.Json.JsonEither (JsonEither(..))
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Lens', over, preview, review, set, view)
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, IProp, br_, button, code_, div, div_, h2_, h3_, hr_, input, label, p_, pre_, small, small_, strong_, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onChecked, onClick, onDragEnd, onDragEnter, onDragLeave, onDragOver, onDragStart, onDrop, onValueInput)
import Halogen.HTML.Properties (InputType(..), checked, class_, classes, disabled, draggable, for, id_, name, placeholder, required, type_, value)
import Halogen.HTML.Properties as HP
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(..))
import Language.Haskell.Interpreter as PI
import Ledger.Extra (_LowerBoundExtended, _LowerBoundInclusive, _UpperBoundExtended, _UpperBoundInclusive, _ivFrom, _ivTo, humaniseInterval)
import Ledger.Interval (Extended(..), Interval, _Interval)
import Ledger.Slot (Slot(..))
import Ledger.Value (Value)
import Network.RemoteData (RemoteData(Loading, NotAsked, Failure, Success))
import Playground.Types (ContractCall(..), EvaluationResult, FunctionSchema, PlaygroundError(..), Simulation(..), _CallEndpoint, _EndpointName, _FunctionSchema)
import Prelude (const, map, mempty, not, pure, show, zero, (#), ($), (+), (/=), (<$>), (<<<), (<>), (==), (>))
import Prim.TypeError (class Warn, Text)
import Schema (FormSchema, FormArgumentF(..))
import Validation (ValidationError, WithPath, joinPath, showPathValue, validate)
import ValueEditor (valueForm)
import Wallet (walletIdPane, walletsPane)
import Wallet.Emulator.Wallet (Wallet)
import Web.Event.Event (Event)
import Web.HTML.Event.DragEvent (DragEvent)

simulationPane ::
  forall m.
  Value ->
  Maybe Int ->
  Array (FunctionSchema FormSchema) ->
  Cursor Simulation ->
  WebData (JsonEither PlaygroundError EvaluationResult) ->
  ComponentHTML HAction ChildSlots m
simulationPane initialValue actionDrag endpointSignatures simulations evaluationResult = case current simulations of
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
      div_
        [ simulationsNav simulations
        , walletsPane endpointSignatures initialValue simulationWallets
        , br_
        , actionsPane isValidWallet actionDrag simulationActions evaluationResult
        ]
  Nothing ->
    div_
      [ text "Click the "
      , strong_ [ text "Editor" ]
      , text " tab above and compile a contract to get started."
      ]

simulationsNav :: forall p. Cursor Simulation -> HTML p HAction
simulationsNav simulations =
  div
    [ id_ "simulation-nav"
    , classes [ btnGroup, btnGroupSmall ]
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
  [ button
      [ id_ $ "simulation-nav-item-" <> show index
      , classes $ buttonClasses <> [ simulationNavItemNameClass ]
      , onClick $ const $ Just $ SetSimulationSlot index
      ]
      [ text simulationName ]
  , if canClose then
      button
        [ id_ $ "simulation-nav-item-" <> show index <> "-remove"
        , classes $ buttonClasses <> [ simulationNavItemCloseClass ]
        , onClick $ const $ Just $ RemoveSimulationSlot index
        ]
        [ icon Close ]
    else
      Bootstrap.empty
  ]
  where
  buttonClasses =
    [ btn, simulationNavItemClass ]
      <> if activeIndex == index then [ btnPrimary ] else [ btnInfo ]

simulationNavItemClass :: ClassName
simulationNavItemClass = ClassName "simulation-nav-item"

simulationNavItemNameClass :: ClassName
simulationNavItemNameClass = ClassName "simulation-nav-item-name"

simulationNavItemCloseClass :: ClassName
simulationNavItemCloseClass = ClassName "simulation-nav-item-close"

addSimulationControl :: forall p. HTML p HAction
addSimulationControl =
  button
    [ id_ "simulation-nav-item-add"
    , classes [ btn, btnInfo, simulationNavItemClass ]
    , onClick $ const $ Just $ AddSimulationSlot
    ]
    [ icon Plus ]

actionsPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Array SimulatorAction -> WebData (JsonEither PlaygroundError EvaluationResult) -> HTML p HAction
actionsPane isValidWallet actionDrag actions evaluationResult =
  div_
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

actionPane :: forall p. (Wallet -> Boolean) -> Maybe Int -> Int -> SimulatorAction -> Tuple String (HTML p HAction)
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
                [ cardBody_
                    [ div
                        [ classes [ badge, badgePrimary, ClassName "badge-action" ] ]
                        [ text $ show (index + 1) ]
                    , button
                        [ classes [ btn, btnInfo, pullRight ]
                        , onClick $ const $ Just $ ModifyActions $ RemoveAction index
                        ]
                        [ icon Close ]
                    , actionPaneBody index action
                    ]
                ]
            ]
        ]

actionPaneBody :: forall p. Int -> ContractCall (Fix FormArgumentF) -> HTML p HAction
actionPaneBody index (CallEndpoint { caller, argumentValues }) =
  div_
    [ h3_
        [ walletIdPane caller
        , text ": "
        , text $ view (_FunctionSchema <<< _endpointName <<< _EndpointName) argumentValues
        ]
    , actionArgumentForm index $ view (_FunctionSchema <<< _arguments) argumentValues
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
            , onIntInput (ModifyActions <<< SetPayToWalletRecipient index <<< review _walletId)
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
                    , onIntInput $ ModifyActions <<< SetWaitTime index
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
                    , onIntInput $ ModifyActions <<< SetWaitUntilTime index <<< review _InSlot
                    ]
                ]
            ]
        ]
    ]

waitTypeButtons :: forall p. Int -> Either Slot Int -> HTML p HAction
waitTypeButtons index wait =
  btnGroup_
    [ button
        ( case wait of
            Left slot -> [ classes inactiveClasses, onClick $ const $ Just $ ModifyActions $ SetWaitTime index $ view _InSlot slot ]
            Right _ -> [ classes activeClasses ]
        )
        [ text "Wait For..." ]
    , button
        ( case wait of
            Right blocks -> [ classes inactiveClasses, onClick $ const $ Just $ ModifyActions $ SetWaitUntilTime index $ review _InSlot blocks ]
            Left _ -> [ classes activeClasses ]
        )
        [ text "Wait Until..." ]
    ]
  where
  activeClasses = [ btn, btnSmall, btnPrimary ]

  inactiveClasses = [ btn, btnSmall, btnInfo ]

validationClasses ::
  forall a.
  FormArgument ->
  Maybe a ->
  Array ClassName
validationClasses arg Nothing = [ ClassName "error" ]

validationClasses arg (Just _) = []

actionArgumentClass :: Array String -> Array ClassName
actionArgumentClass ancestors =
  [ ClassName "action-argument"
  , ClassName $ "action-argument-" <> Array.intercalate "-" ancestors
  ]

actionArgumentForm :: forall p. Int -> Array FormArgument -> HTML p HAction
actionArgumentForm index arguments =
  div [ class_ wasValidated ]
    ( Array.intercalate
        [ hr_ ]
        ( Array.mapWithIndex
            (\i argument -> [ PopulateAction index i <$> actionArgumentField [ show i ] false argument ])
            arguments
        )
    )

actionArgumentField ::
  forall p.
  Warn (Text "We're still not handling the Unsupported case.") =>
  Warn (Text "We're still not handling the FormMaybe case.") =>
  Warn (Text "The Hex fields should be forced to comply to [0-9a-fA-F].") =>
  Array String ->
  Boolean ->
  FormArgument ->
  HTML p FormEvent
actionArgumentField ancestors _ arg@(Fix FormUnitF) = Bootstrap.empty

actionArgumentField ancestors _ arg@(Fix (FormBoolF b)) =
  formCheck_
    [ input
        [ type_ InputCheckbox
        , id_ elementId
        , classes (Array.cons formCheckInput (actionArgumentClass ancestors))
        , checked b
        , onChecked (Just <<< SetField <<< SetBoolField)
        ]
    , label
        [ class_ formCheckLabel
        , for elementId
        ]
        [ text (if b then "True" else "False") ]
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]
  where
  elementId = String.joinWith "-" ancestors

actionArgumentField ancestors _ arg@(Fix (FormIntF n)) =
  div_
    [ input
        [ type_ InputNumber
        , classes (Array.cons formControl (actionArgumentClass ancestors))
        , value $ maybe "" show n
        , required true
        , placeholder "Int"
        , onValueInput (Just <<< SetField <<< SetIntField <<< Int.fromString)
        ]
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]

actionArgumentField ancestors _ arg@(Fix (FormStringF s)) =
  div_
    [ input
        [ type_ InputText
        , classes (Array.cons formControl (actionArgumentClass ancestors))
        , value $ fromMaybe "" s
        , required true
        , placeholder "String"
        , onValueInput (Just <<< SetField <<< SetStringField)
        ]
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]

actionArgumentField ancestors _ arg@(Fix (FormRadioF options s)) =
  formGroup_
    [ div_ (radioItem <$> options)
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]
  where
  radioItem :: String -> HTML p FormEvent
  radioItem option =
    let
      elementId = String.joinWith "-" (ancestors <> [ option ])
    in
      formCheck_
        [ input
            [ type_ InputRadio
            , id_ elementId
            , classes (Array.cons formCheckInput (actionArgumentClass ancestors))
            , name option
            , value option
            , required (s == Nothing)
            , onValueInput (Just <<< SetField <<< SetRadioField)
            , checked (Just option == s)
            ]
        , label
            [ class_ formCheckLabel
            , for elementId
            ]
            [ text option ]
        ]

actionArgumentField ancestors _ arg@(Fix (FormHexF s)) =
  div_
    [ input
        [ type_ InputText
        , classes (Array.cons formControl (actionArgumentClass ancestors))
        , value $ fromMaybe "" s
        , required true
        , placeholder "String"
        , onValueInput (Just <<< SetField <<< SetHexField)
        ]
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]

actionArgumentField ancestors isNested (Fix (FormTupleF subFieldA subFieldB)) =
  row_
    [ col_ [ SetSubField 1 <$> actionArgumentField (Array.snoc ancestors "_1") true subFieldA ]
    , col_ [ SetSubField 2 <$> actionArgumentField (Array.snoc ancestors "_2") true subFieldB ]
    ]

actionArgumentField ancestors isNested (Fix (FormArrayF schema subFields)) =
  div_
    [ Keyed.div [ nesting isNested ]
        (mapWithIndex subFormContainer subFields)
    , button
        [ classes [ btn, btnInfo ]
        , onClick $ const $ Just AddSubField
        ]
        [ icon Plus ]
    ]
  where
  subFormContainer i field =
    show i
      /\ formGroup_
          [ row_
              [ col10_
                  [ SetSubField i <$> actionArgumentField (Array.snoc ancestors (show i)) true field ]
              , col2_
                  [ button
                      [ classes [ btn, btnLink ]
                      , onClick $ const $ Just (RemoveSubField i)
                      ]
                      [ icon Trash ]
                  ]
              ]
          ]

actionArgumentField ancestors isNested (Fix (FormObjectF subFields)) =
  div [ nesting isNested ]
    (mapWithIndex (\i (JsonTuple field) -> map (SetSubField i) (subForm field)) subFields)
  where
  subForm (name /\ arg) =
    ( formGroup_
        [ label [ for name ] [ text name ]
        , actionArgumentField (Array.snoc ancestors name) true arg
        ]
    )

actionArgumentField ancestors isNested (Fix (FormSlotRangeF interval)) =
  div [ class_ formGroup, nesting isNested ]
    [ label [ for "interval" ] [ text "Interval" ]
    , formRow_
        [ label [ for "ivFrom", classes [ col, colFormLabel ] ] [ text "From" ]
        , label [ for "ivTo", classes [ col, colFormLabel ] ] [ text "To" ]
        ]
    , formRow_
        [ let
            extensionLens :: Lens' (Interval Slot) (Extended Slot)
            extensionLens = _Interval <<< _ivFrom <<< _LowerBoundExtended

            inclusionLens :: Lens' (Interval Slot) Boolean
            inclusionLens = _Interval <<< _ivFrom <<< _LowerBoundInclusive
          in
            div [ classes [ col, extentFieldClass ] ]
              [ inputGroup_
                  [ inputGroupPrepend_
                      [ extentFieldExtendedButton extensionLens NegInf
                      , extentFieldInclusionButton inclusionLens StepBackward Reverse
                      ]
                  , extentFieldInput extensionLens
                  ]
              ]
        , let
            extensionLens :: Lens' (Interval Slot) (Extended Slot)
            extensionLens = _Interval <<< _ivTo <<< _UpperBoundExtended

            inclusionLens :: Lens' (Interval Slot) Boolean
            inclusionLens = _Interval <<< _ivTo <<< _UpperBoundInclusive
          in
            div [ classes [ col, extentFieldClass ] ]
              [ inputGroup_
                  [ extentFieldInput extensionLens
                  , inputGroupAppend_
                      [ extentFieldInclusionButton inclusionLens StepForward Play
                      , extentFieldExtendedButton extensionLens PosInf
                      ]
                  ]
              ]
        ]
    , small
        [ classes [ formText, textMuted ] ]
        [ text $ humaniseInterval interval
        ]
    ]
  where
  extentFieldClass = ClassName "extent-field"

  extentFieldInclusionButton :: Lens' (Interval Slot) Boolean -> Icon -> Icon -> HTML p FormEvent
  extentFieldInclusionButton inclusionLens inclusionIcon exclusionIcon =
    button
      [ classes [ btn, btnSmall, btnPrimary ]
      , onClick $ const $ Just $ SetField $ SetSlotRangeField $ over inclusionLens not interval
      ]
      [ icon
          $ if view inclusionLens interval then
              inclusionIcon
            else
              exclusionIcon
      ]

  extentFieldExtendedButton :: Lens' (Interval Slot) (Extended Slot) -> Extended Slot -> HTML p FormEvent
  extentFieldExtendedButton extensionLens value =
    button
      [ classes
          [ btn
          , btnSmall
          , if view extensionLens interval == value then
              btnPrimary
            else
              btnInfo
          ]
      , onClick $ const $ Just $ SetField $ SetSlotRangeField $ set extensionLens value interval
      ]
      [ icon Infinity ]

  extentFieldInput :: Lens' (Interval Slot) (Extended Slot) -> HTML p FormEvent
  extentFieldInput extensionLens =
    input
      [ type_ InputNumber
      , class_ formControl
      , HP.min zero
      , value
          $ case view extensionLens interval of
              Finite (Slot slot) -> show slot.getSlot
              _ -> mempty
      , onValueInput $ map (\n -> SetField (SetSlotRangeField (set extensionLens (Finite (Slot { getSlot: n })) interval))) <<< Int.fromString
      ]

actionArgumentField ancestors isNested (Fix (FormValueF value)) =
  div [ nesting isNested ]
    [ label [ for "value" ] [ text "Value" ]
    , valueForm (SetField <<< SetValueField) value
    ]

actionArgumentField _ _ (Fix (FormMaybeF dataType child)) =
  div_
    [ text "Unsupported Maybe"
    , code_ [ text $ show dataType ]
    , code_ [ text $ show child ]
    ]

actionArgumentField _ _ (Fix (FormUnsupportedF description)) =
  div_
    [ text "Unsupported"
    , code_ [ text description ]
    ]

nesting :: forall r i. Boolean -> IProp ( "class" :: String | r ) i
nesting true = classes [ ClassName "nested" ]

nesting false = classes []

validationFeedback :: forall p i. Array (WithPath ValidationError) -> HTML p i
validationFeedback [] = validFeedback_ [ nbsp ]

validationFeedback errors = invalidFeedback_ (div_ <<< pure <<< text <<< showPathValue <$> errors)

addWaitActionPane :: forall p. Int -> Tuple String (HTML p HAction)
addWaitActionPane index =
  Tuple "add-wait"
    $ responsiveThird
        [ div
            [ class_ $ ClassName "add-wait-action" ]
            [ div
                ( [ class_ card
                  , onClick $ const $ Just $ ModifyActions $ AddWaitAction 10
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

evaluateActionsPane :: forall p. WebData (JsonEither PlaygroundError EvaluationResult) -> Array SimulatorAction -> HTML p HAction
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

  btnClass (Success (JsonEither (Left _))) _ = btnDanger

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
