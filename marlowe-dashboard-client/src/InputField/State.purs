module InputField.State
  ( dummyState
  , initialState
  , handleAction
  , getBigIntegerValue
  , validate
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Array (head, last, length, take)
import Data.BigInteger (BigInteger)
import Data.BigInteger (fromInt, fromString) as BigInteger
import Data.Int (pow)
import Data.Lens (assign, set, use, view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM, modify_)
import Humanize (humanizeValue)
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
      Just (DecimalFormat decimals _) -> humanizeValue decimals zero
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

-- This handler is used for number inputs instead of SetValue. Since `getBigIntegerValue` and
-- `humanizeValue` are essentially inverses of each other, you might think it doesn't do anything
-- differently from what plain old SetValue does. But the difference is that this version sanitizes
-- the user input, replacing empty strings with "0" and enforcing the right number of decimal
-- places.
handleAction (SetFormattedValue numberFormat value) =
  let
    decimals = case numberFormat of
      DefaultFormat -> zero
      DecimalFormat d _ -> d

    bigIntegerValue = getBigIntegerValue decimals value

    newValue = humanizeValue decimals bigIntegerValue
  in
    modify_
      $ set _value newValue
      <<< set _pristine false

-- This seemingly pointless action is used to force an update onKeyUp for number inputs. This is
-- needed because some edits to numeric inputs don't trigger the onValueChange handler. I *think*
-- this is because Halogen doesn't bubble the event up if the result of `parseFloat(value)` doesn't
-- change or is `NaN` - but I haven't investigated it thoroughly.
handleAction RefreshFormattedValue = do
  value <- use _value
  assign _value value

handleAction (SetValueFromDropdown value) = do
  handleAction $ SetValue value
  assign _dropdownOpen false

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
-- This function is essentially the inverse of humanizeValue, except that it doesn't mind if the
-- format of the input string is incorrect (e.g. with the wrong number of decimal places), and it
-- returns zero in the case of input that can't be parsed as a number. Since we store the value in
-- the state as a string (the output of humanizeValue), we need this function to extract the
-- BigInteger value from that string. Now, since humanizeValue divides the value by decimals^10,
-- here we need to multiply by the same. But the process is a bit more involved than just parsing
-- as a Number and then multplying and converting to a BigInteger, because after the multiplication
-- the value can easily get too large to handle as a Number. So instead we split the string into
-- the decimal and fractional part, and parse both separately as BigIntegers before stitching it
-- all back together.
getBigIntegerValue :: Int -> String -> BigInteger
getBigIntegerValue decimals value =
  let
    valueBits = take 2 $ split (Pattern ".") value

    decimalString = if value /= "" then fromMaybe "0" $ head valueBits else "0"

    fractionalString = if length valueBits > 1 then fromMaybe "0" $ last valueBits else "0"

    multiplier = BigInteger.fromInt $ pow 10 decimals

    dec = fromMaybe zero $ BigInteger.fromString decimalString

    frac = fromMaybe zero $ BigInteger.fromString fractionalString
  in
    (dec * multiplier) + frac

validate :: forall e. InputFieldError e => State e -> Maybe e
validate state =
  let
    value = view _value state

    validator = view _validator state
  in
    validator value
