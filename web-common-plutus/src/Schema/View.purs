module Schema.View (actionArgumentForm) where

import Prelude hiding (div)
import Bootstrap (btn, btnInfo, btnLink, btnPrimary, btnSmall, col, col10_, col2_, colFormLabel, formCheckInput, formCheckLabel, formCheck_, formControl, formGroup, formGroup_, formRow_, formText, inputGroupAppend_, inputGroupPrepend_, inputGroup_, invalidFeedback_, row_, textMuted, validFeedback_, wasValidated)
import Bootstrap as Bootstrap
import Data.Array as Array
import Data.BigInteger as BigInteger
import Data.Functor.Foldable (Fix(..))
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int as Int
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Lens', over, set, view)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String as String
import Data.Tuple.Nested ((/\))
import Halogen (ClassName(..))
import Halogen.HTML (HTML, button, code_, div, div_, input, label, small, text)
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onChecked, onClick, onValueInput)
import Halogen.HTML.Properties (IProp, InputType(..), checked, class_, classes, for, id_, name, placeholder, required, type_, value)
import Halogen.HTML.Properties as HP
import Icons (Icon(..), icon)
import Ledger.Extra (_LowerBoundExtended, _LowerBoundInclusive, _UpperBoundExtended, _UpperBoundInclusive, _ivFrom, _ivTo, humaniseSlotInterval, humaniseTimeInterval)
import Plutus.V1.Ledger.Interval (Extended(..), Interval, _Interval)
import Plutus.V1.Ledger.Slot (Slot(..))
import Plutus.V1.Ledger.Time (POSIXTime(..))
import Prim.TypeError (class Warn, Text)
import Schema (FormArgumentF(..))
import Schema.Types (FieldEvent(..), FormArgument, FormEvent(..))
import Validation (ValidationError, WithPath, joinPath, showPathValue, validate)
import ValueEditor (valueForm)

actionArgumentForm ::
  forall p i.
  Int ->
  (FormEvent -> i) ->
  FormArgument ->
  HTML p i
actionArgumentForm index wrapper argument =
  div [ class_ wasValidated ]
    [ wrapper <$> actionArgumentField [ show index ] false argument ]

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

actionArgumentField ancestors _ arg@(Fix (FormIntegerF n)) =
  div_
    [ input
        [ type_ InputNumber
        , classes (Array.cons formControl (actionArgumentClass ancestors))
        , value $ maybe "" show n
        , required true
        , placeholder "Integer"
        , onValueInput (Just <<< SetField <<< SetBigIntegerField <<< BigInteger.fromString)
        ]
    , validationFeedback (joinPath ancestors <$> validate arg)
    ]

actionArgumentField ancestors _ arg@(Fix (FormStringF s)) =
  div_
    [ input
        [ type_ InputText
        , classes (Array.cons formControl (actionArgumentClass ancestors))
        , value $ fromMaybe "" s
        -- empty text inputs give `Just ""` as a value, which might be wanted,
        -- so don't mark these fields as required
        , required false
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
  div_
    [ formGroup_
        [ SetSubField 1 <$> actionArgumentField (Array.snoc ancestors "_1") true subFieldA ]
    , formGroup_
        [ SetSubField 2 <$> actionArgumentField (Array.snoc ancestors "_2") true subFieldB ]
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

actionArgumentField ancestors isNested (Fix (FormPOSIXTimeRangeF interval)) =
  div [ class_ formGroup, nesting isNested ]
    [ label [ for "interval" ] [ text "Interval" ]
    , formRow_
        [ label [ for "ivFrom", classes [ col, colFormLabel ] ] [ text "From" ]
        , label [ for "ivTo", classes [ col, colFormLabel ] ] [ text "To" ]
        ]
    , formRow_
        [ let
            extensionLens :: Lens' (Interval POSIXTime) (Extended POSIXTime)
            extensionLens = _Interval <<< _ivFrom <<< _LowerBoundExtended

            inclusionLens :: Lens' (Interval POSIXTime) Boolean
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
            extensionLens :: Lens' (Interval POSIXTime) (Extended POSIXTime)
            extensionLens = _Interval <<< _ivTo <<< _UpperBoundExtended

            inclusionLens :: Lens' (Interval POSIXTime) Boolean
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
        [ text $ humaniseTimeInterval interval
        ]
    ]
  where
  extentFieldClass = ClassName "extent-field"

  extentFieldInclusionButton :: Lens' (Interval POSIXTime) Boolean -> Icon -> Icon -> HTML p FormEvent
  extentFieldInclusionButton inclusionLens inclusionIcon exclusionIcon =
    button
      [ classes [ btn, btnSmall, btnPrimary ]
      , onClick $ const $ Just $ SetField $ SetPOSIXTimeRangeField $ over inclusionLens not interval
      ]
      [ icon
          $ if view inclusionLens interval then
              inclusionIcon
            else
              exclusionIcon
      ]

  extentFieldExtendedButton :: Lens' (Interval POSIXTime) (Extended POSIXTime) -> Extended POSIXTime -> HTML p FormEvent
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
      , onClick $ const $ Just $ SetField $ SetPOSIXTimeRangeField $ set extensionLens value interval
      ]
      [ icon Infinity ]

  extentFieldInput :: Lens' (Interval POSIXTime) (Extended POSIXTime) -> HTML p FormEvent
  extentFieldInput extensionLens =
    input
      [ type_ InputNumber
      , class_ formControl
      , HP.min zero
      , value
          $ case view extensionLens interval of
              Finite (POSIXTime time) -> show time.getPOSIXTime
              _ -> mempty
      , onValueInput $ map (\n -> SetField (SetPOSIXTimeRangeField (set extensionLens (Finite (POSIXTime { getPOSIXTime: n })) interval))) <<< BigInteger.fromString
      ]

actionArgumentField ancestors isNested (Fix (FormValueF value)) =
  div
    [ nesting isNested ]
    [ valueForm (SetField <<< SetValueField) value ]

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

actionArgumentClass :: Array String -> Array ClassName
actionArgumentClass ancestors =
  [ ClassName "action-argument"
  , ClassName $ "action-argument-" <> Array.intercalate "-" ancestors
  ]

validationFeedback :: forall p i. Array (WithPath ValidationError) -> HTML p i
validationFeedback [] = validFeedback_ []

validationFeedback errors = invalidFeedback_ (div_ <<< pure <<< text <<< showPathValue <$> errors)

nesting :: forall r i. Boolean -> IProp ( "class" :: String | r ) i
nesting true = classes [ ClassName "nested" ]

nesting false = classes []
