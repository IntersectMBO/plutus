module InputField.State
  ( dummyState
  , initialState
  , handleAction
  , getBigIntegerValue
  , validate
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Array (head, last)
import Data.Array (length, take) as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger (fromInt, fromString) as BigInteger
import Data.Int (pow) as Int
import Data.Lens (assign, set, use, view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split, splitAt)
import Data.String (drop, length, take) as String
import Data.String.Extra (leftPadTo, rightPadTo)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import InputField.Lenses (_dropdownLocked, _dropdownOpen, _pristine, _validator, _value)
import InputField.Types (class InputFieldError, Action(..), State)
import Marlowe.Extended.Metadata (NumberFormat(..))

-- see note [dummyState] in MainFrame.State
dummyState :: forall e. InputFieldError e => State e
dummyState = initialState Nothing

initialState :: forall e. InputFieldError e => Maybe NumberFormat -> State e
initialState mNumberFormat =
  let
    initialValue = case mNumberFormat of
      Just (DecimalFormat decimals _) -> formatBigIntegerValue decimals zero
      _ -> mempty
  in
    { value: initialValue
    , pristine: true
    , validator: const Nothing
    , dropdownOpen: false
    , dropdownLocked: false
    }

handleAction ::
  forall m e slots msg.
  MonadAff m =>
  MonadAsk Env m =>
  InputFieldError e =>
  Action e -> HalogenM (State e) (Action e) slots msg m Unit
handleAction (SetValue value) =
  modify_
    $ set _value value
    <<< set _pristine false

handleAction (SetValueFromDropdown value) = do
  handleAction $ SetValue value
  assign _dropdownOpen false

handleAction (FormatValue numberFormat) = do
  currentValue <- use _value
  let
    decimals = case numberFormat of
      DefaultFormat -> zero
      DecimalFormat d _ -> d

    bigIntegerValue = getBigIntegerValue decimals currentValue

    formattedValue = formatBigIntegerValue decimals bigIntegerValue
  handleAction $ SetValue formattedValue

handleAction (SetValidator validator) = assign _validator validator

handleAction (SetDropdownOpen dropdownOpen) = assign _dropdownOpen dropdownOpen

handleAction (SetDropdownLocked dropdownLocked) = assign _dropdownLocked dropdownLocked

handleAction Reset =
  modify_
    $ set _value mempty
    <<< set _pristine true
    <<< set _validator (const Nothing)
    <<< set _dropdownOpen false

------------------------------------------------------------
-- Numeric inputs are interpreted as BigIntegers, but are entered and stored in the state as
-- strings, partly because they are strings in the DOM, but mainly because we want to display them
-- as numbers with a fixed number of decimal places (e.g. showing 2,500,001 lovelace as
-- "₳2.500001", or 120 cents as "$1.20"). To this end, we need functions to convert BigIntegers to
-- suitably formatted strings, and back again. Two things to note about these functions:
-- 1. The implementation of `getBitIntegerValue` is more convoluted than just parsing as a Number,
--    multplying up to account for the decimal places, and then converting to a BigInteger. This is
--    because after the multiplication the value can easily get too large to handle as a Number. So
--    instead we split the string into the decimal and fractional part, and parse both separately
--    as BigIntegers before stitching it all back together.
-- 2. It is tempting to put `formatBigIntegerValue` in the `Humanize` module, and use the standard
--    number formatter used there. And so that's what I tried first. But on playing around with it,
--    it became apparent that this standard number formatter can't handle numbers beyond a certain
--    size. And since we need a bespoke solution that's only used in this particular case, it seems
--    better to just keep it in this module.
getBigIntegerValue :: Int -> String -> BigInteger
getBigIntegerValue decimals value =
  let
    { isNegative, absoluteValue } =
      if String.take 1 value == "-" then
        { isNegative: true, absoluteValue: String.drop 1 value }
      else
        { isNegative: false, absoluteValue: value }

    valueBits = Array.take 2 $ split (Pattern ".") absoluteValue

    decimalString = if absoluteValue == "" then "0" else fromMaybe "0" $ head valueBits

    fractionalString = if Array.length valueBits < 2 then "0" else fromMaybe "0" $ last valueBits

    -- if zeros have been deleted from the end of the string, the fractional part will be wrong
    correctedFractionalString = String.take decimals $ rightPadTo decimals "0" fractionalString

    multiplier = BigInteger.fromInt $ Int.pow 10 decimals

    dec = fromMaybe zero $ BigInteger.fromString decimalString

    frac = fromMaybe zero $ BigInteger.fromString $ String.take decimals $ correctedFractionalString
  in
    if isNegative then
      -((dec * multiplier) + frac)
    else
      (dec * multiplier) + frac

-- The basic idea of this function is to take the default string representation (`show value`),
-- split it where the decimal point is supposed to go, and join the two parts with a decimal point
-- in the middle. Simple enough, but there are a few things to watch out for:
-- 1. The default string representation needs left zero padding to a minimum length of `decimals`,
--    otherwise small values (i.e where the absolute value of `value / (decimals ^ 10)` is less
--    than 1) get the wrong fractionalString.
-- 2. If the value is negative, the minus sign needs to go to the left of the left zero padding.
-- 3. Small positive values will have no decimalString following the split, and the decimal string
--    for small negative values will just be a minus sign, so a zero needs to be added in these
--    cases.
formatBigIntegerValue :: Int -> BigInteger -> String
formatBigIntegerValue decimals value =
  let
    string =
      if value < zero then
        "-" <> (leftPadTo decimals "0" $ String.drop 1 $ show value)
      else
        leftPadTo decimals "0" $ show value

    len = String.length string

    { after: fractionalString, before } = splitAt (len - decimals) string

    decimalString = case before of
      "" -> "0"
      "-" -> "-0"
      _ -> before
  in
    decimalString <> "." <> fractionalString

validate :: forall e. InputFieldError e => State e -> Maybe e
validate state =
  let
    value = view _value state

    validator = view _validator state
  in
    validator value
