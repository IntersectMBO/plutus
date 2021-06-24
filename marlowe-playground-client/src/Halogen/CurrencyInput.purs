module Halogen.CurrencyInput where

import Prelude hiding (div)
import Data.Array (concat, drop, dropWhile, filter, length, replicate, take)
import Data.BigInteger (BigInteger, fromString)
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid (guard)
import Data.String (trim)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.Traversable (for)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Effect.Unsafe (unsafePerformEffect)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, div, input, text)
import Halogen.HTML.Events (onChange, onFocus, onInput, onKeyDown)
import Halogen.HTML.Properties (InputType(..), type_, value)
import Web.Event.Event (currentTarget)
import Web.Event.Internal.Types (EventTarget)
import Web.UIEvent.FocusEvent as FocusEvent
import Web.UIEvent.KeyboardEvent as KeyboardEvent

foreign import setOldValues_ :: EffectFn1 EventTarget Unit

foreign import checkChange_ :: EffectFn1 EventTarget Unit

foreign import formatValue_ :: EffectFn2 EventTarget Int Unit

foreign import formatValueString_ :: EffectFn2 String Int String

foreign import setValue_ :: EffectFn2 EventTarget String Unit

foreign import onChangeHandler_ :: EffectFn2 EventTarget Int String

setOldValues :: EventTarget -> Effect Unit
setOldValues = runEffectFn1 setOldValues_

checkChange :: EventTarget -> Effect Unit
checkChange = runEffectFn1 checkChange_

setValue :: EventTarget -> String -> Effect Unit
setValue = runEffectFn2 setValue_

onChangeHandler :: EventTarget -> Int -> Effect String
onChangeHandler = runEffectFn2 onChangeHandler_

currencyInput :: forall p a. Array String -> BigInteger -> String -> Int -> (Maybe BigInteger -> Maybe a) -> HTML p a
currencyInput classList number prefix rawNumDecimals onValueChangeHandler =
  div [ classNames ([ "bg-gray-light", "flex", "items-center", "p-0", "m-0", "border-solid", "border", "rounded-sm", "overflow-hidden", "box-border", "focus-within:ring-1", "focus-within:ring-black" ] <> classList) ]
    ( ( guard hasPrefix
          [ div [ classNames [ "flex-none", "px-2", "py-0", "box-border", "self-center" ] ]
              [ text prefix ]
          ]
      )
        <> [ input
              [ classNames [ "flex-1", "text-center", "box-border", "self-stretch", "border-0", "outline-none" ]
              , onFocus
                  ( \ev ->
                      maybe Nothing
                        ( \target ->
                            unsafePerformEffect
                              $ do
                                  setOldValues target
                                  pure Nothing
                        )
                        (currentTarget (FocusEvent.toEvent ev))
                  )
              , onKeyDown
                  ( \ev ->
                      maybe Nothing
                        ( \target ->
                            unsafePerformEffect
                              $ do
                                  setOldValues target
                                  pure Nothing
                        )
                        (currentTarget (KeyboardEvent.toEvent ev))
                  )
              , onChange
                  ( \ev ->
                      maybe Nothing
                        ( \target ->
                            unsafePerformEffect
                              $ do
                                  res <- onChangeHandler target numDecimals
                                  let
                                    mObtainedBigNumStr = fromString $ filterPoint res
                                  void $ for mObtainedBigNumStr (\x -> setValue target $ renderBigIntegerAsCurrency x numDecimals)
                                  pure $ onValueChangeHandler $ mObtainedBigNumStr
                        )
                        (currentTarget ev)
                  )
              , onInput
                  ( \ev ->
                      maybe Nothing
                        ( \target ->
                            unsafePerformEffect
                              $ do
                                  checkChange target
                                  pure Nothing
                        )
                        (currentTarget ev)
                  )
              , type_ InputText
              , value (renderBigIntegerAsCurrency number numDecimals)
              ]
          ]
    )
  where
  numDecimals = max 0 rawNumDecimals

  hasPrefix = trim prefix /= ""

  filterPoint = fromCharArray <<< filter (\x -> x /= '.') <<< toCharArray

renderBigIntegerAsCurrency :: BigInteger -> Int -> String
renderBigIntegerAsCurrency number numDecimals = fromCharArray numberStr
  where
  absValStr = replicate (numDecimals + 1) '0' <> toCharArray (show (if number < zero then -number else number))

  numDigits = length absValStr

  numDigitsBeforeSeparator = numDigits - numDecimals

  prefixStr = if number < zero then [ '-' ] else []

  digitsNoZeros = dropWhile (\x -> x == '0') $ take numDigitsBeforeSeparator absValStr

  digitsBeforeSeparator = if digitsNoZeros == [] then [ '0' ] else digitsNoZeros

  digitsAfterSeparator = take numDecimals $ drop numDigitsBeforeSeparator (concat [ absValStr, replicate numDecimals '0' ])

  numberStr = concat ([ prefixStr, digitsBeforeSeparator ] <> if digitsAfterSeparator /= [] then [ [ '.' ], digitsAfterSeparator ] else [])
