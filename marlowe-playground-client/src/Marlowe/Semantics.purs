module Marlowe.Semantics where

import Prelude
import Data.BigInteger (BigInteger, fromInt, quot, rem)
import Data.Foldable (class Foldable, any, foldl)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Integral (class Integral)
import Data.Lens (Lens', over, to, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..), fromFoldable, null, reverse, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Num (class Num)
import Data.Real (class Real)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty, text)

type PubKey
  = String

data Party
  = PK PubKey
  | Role TokenName

derive instance genericParty :: Generic Party _

derive instance eqParty :: Eq Party

derive instance ordParty :: Ord Party

instance showParty :: Show Party where
  show = genericShow

instance prettyParty :: Pretty Party where
  pretty = genericPretty

instance hasArgsParty :: Args Party where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

type Timeout
  = Slot

type Money
  = Assets

type CurrencySymbol
  = String

type TokenName
  = String

data Token
  = Token CurrencySymbol TokenName

derive instance genericToken :: Generic Token _

derive instance eqToken :: Eq Token

derive instance ordToken :: Ord Token

instance showToken :: Show Token where
  show tok = genericShow tok

instance prettyToken :: Pretty Token where
  pretty = genericPretty

instance hasArgsToken :: Args Token where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

type ChosenNum
  = BigInteger

type Accounts
  = Map (Tuple AccountId Token) BigInteger

type ChoiceName
  = String

newtype Assets
  = Assets (Map CurrencySymbol (Map TokenName BigInteger))

derive instance genericAssets :: Generic Assets _

derive instance newtypeAssets :: Newtype Assets _

derive instance eqAssets :: Eq Assets

derive newtype instance showAssets :: Show Assets

instance semigroupAssets :: Semigroup Assets where
  append (Assets a) (Assets b) = Assets (Map.unionWith f a b)
    where
    f = Map.unionWith (+)

instance monoidAssets :: Monoid Assets where
  mempty = Assets mempty

newtype Slot
  = Slot BigInteger

derive instance genericSlot :: Generic Slot _

derive instance newtypeSlot :: Newtype Slot _

derive instance eqSlot :: Eq Slot

derive instance ordSlot :: Ord Slot

derive newtype instance showSlot :: Show Slot

derive newtype instance semiRingSlot :: Semiring Slot

derive newtype instance ringSlot :: Ring Slot

instance commutativeRingSlot :: CommutativeRing Slot

derive newtype instance euclideanRingSlot :: EuclideanRing Slot

derive newtype instance numSlot :: Num Slot

derive newtype instance realRingSlot :: Real Slot

derive newtype instance integralSlot :: Integral Slot

derive newtype instance prettySlot :: Pretty Slot

derive newtype instance hasArgsSlot :: Args Slot

newtype Ada
  = Lovelace BigInteger

derive instance genericAda :: Generic Ada _

derive instance newtypeAda :: Newtype Ada _

derive instance eqAda :: Eq Ada

derive instance ordAda :: Ord Ada

derive newtype instance showAda :: Show Ada

derive newtype instance integralAda :: Integral Ada

derive newtype instance numAda :: Num Ada

derive newtype instance semiringAda :: Semiring Ada

derive newtype instance ringAda :: Ring Ada

derive newtype instance euclideanRingAda :: EuclideanRing Ada

derive newtype instance realRingAda :: Real Ada

instance commutativeRingAda :: CommutativeRing Ada

data AccountId
  = AccountId BigInteger Party

derive instance genericAccountId :: Generic AccountId _

derive instance eqAccountId :: Eq AccountId

derive instance ordAccountId :: Ord AccountId

instance showAccountId :: Show AccountId where
  show (AccountId number owner) = "(AccountId " <> show number <> " " <> show owner <> ")"

instance prettyAccountId :: Pretty AccountId where
  pretty = genericPretty

instance hasArgsAccountId :: Args AccountId where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

data ChoiceId
  = ChoiceId String Party

derive instance genericChoiceId :: Generic ChoiceId _

derive instance eqChoiceId :: Eq ChoiceId

derive instance ordChoiceId :: Ord ChoiceId

instance showChoiceId :: Show ChoiceId where
  show (ChoiceId name owner) = "(ChoiceId " <> show name <> " " <> show owner <> ")"

instance prettyChoiceId :: Pretty ChoiceId where
  pretty = genericPretty

instance hasArgsChoiceId :: Args ChoiceId where
  hasArgs = genericHasArgs
  hasNestedArgs = genericHasNestedArgs

choiceOwner :: ChoiceId -> Party
choiceOwner (ChoiceId _ owner) = owner

newtype ValueId
  = ValueId String

derive instance genericValueId :: Generic ValueId _

derive instance newtypeValueId :: Newtype ValueId _

derive instance eqValueId :: Eq ValueId

derive instance ordValueId :: Ord ValueId

instance showValueId :: Show ValueId where
  show (ValueId valueId) = show valueId

instance prettyValueId :: Pretty ValueId where
  pretty (ValueId valueId) = text $ show valueId

instance hasArgsValueId :: Args ValueId where
  hasArgs _ = false
  hasNestedArgs _ = false

data Rational
  = Rational BigInteger BigInteger

derive instance genericRational :: Generic Rational _

derive instance eqRational :: Eq Rational

derive instance ordRational :: Ord Rational

instance showRational :: Show Rational where
  show (Rational n d) = "(" <> show n <> "%" <> show d <> ")"

instance prettyRational :: Pretty Rational where
  pretty r = text $ show r

instance hasArgsRational :: Args Rational where
  hasArgs a = false
  hasNestedArgs a = false

data Value
  = AvailableMoney AccountId Token
  | Constant BigInteger
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | Scale Rational Value
  | ChoiceValue ChoiceId Value
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue ValueId

derive instance genericValue :: Generic Value _

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  pretty v = genericPretty v

instance hasArgsValue :: Args Value where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Observation
  = AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseSomething ChoiceId
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

derive instance genericObservation :: Generic Observation _

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

instance showObservation :: Show Observation where
  show o = genericShow o

instance prettyObservation :: Pretty Observation where
  pretty v = genericPretty v

instance hasArgsObservation :: Args Observation where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

validInterval :: SlotInterval -> Boolean
validInterval (SlotInterval from to) = from <= to

above :: Slot -> SlotInterval -> Boolean
above v (SlotInterval _ to) = v >= to

anyWithin :: forall f. Foldable f => Slot -> f SlotInterval -> Boolean
anyWithin v = any (\(SlotInterval from to) -> v >= from && v <= to)

data SlotInterval
  = SlotInterval Slot Slot

derive instance eqSlotInterval :: Eq SlotInterval

derive instance ordSlotInterval :: Ord SlotInterval

instance showSlotInterval :: Show SlotInterval where
  show (SlotInterval from to) = "(Slot " <> show from <> " " <> show to <> ")"

ivFrom :: SlotInterval -> Slot
ivFrom (SlotInterval from _) = from

ivTo :: SlotInterval -> Slot
ivTo (SlotInterval _ to) = to

data Bound
  = Bound BigInteger BigInteger

derive instance genericBound :: Generic Bound _

derive instance eqBound :: Eq Bound

derive instance orBound :: Ord Bound

instance showBound :: Show Bound where
  show = genericShow

instance prettyBound :: Pretty Bound where
  pretty v = genericPretty v

instance hasArgsBound :: Args Bound where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Action
  = Deposit AccountId Party Token Value
  | Choice ChoiceId (Array Bound)
  | Notify Observation

derive instance genericAction :: Generic Action _

derive instance eqAction :: Eq Action

derive instance ordAction :: Ord Action

instance showAction :: Show Action where
  show (Choice cid bounds) = "(Choice " <> show cid <> " " <> show bounds <> ")"
  show v = genericShow v

instance prettyAction :: Pretty Action where
  pretty v = genericPretty v

instance hasArgsAction :: Args Action where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Payee
  = Account AccountId
  | Party Party

derive instance genericPayee :: Generic Payee _

derive instance eqPayee :: Eq Payee

derive instance ordPayee :: Ord Payee

instance showPayee :: Show Payee where
  show v = genericShow v

instance prettyPayee :: Pretty Payee where
  pretty v = genericPretty v

instance hasArgsPayee :: Args Payee where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Case
  = Case Action Contract

derive instance genericCase :: Generic Case _

derive instance eqCase :: Eq Case

derive instance ordCase :: Ord Case

instance showCase :: Show Case where
  show (Case action contract) = "Case " <> show action <> " " <> show contract

instance prettyCase :: Pretty Case where
  pretty v = genericPretty v

instance hasArgsCase :: Args Case where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

data Contract
  = Close
  | Pay AccountId Payee Token Value Contract
  | If Observation Contract Contract
  | When (Array Case) Timeout Contract
  | Let ValueId Value Contract

derive instance genericContract :: Generic Contract _

derive instance eqContract :: Eq Contract

derive instance ordContract :: Ord Contract

instance showContract :: Show Contract where
  show v = genericShow v

instance prettyContract :: Pretty Contract where
  pretty v = genericPretty v

instance hasArgsContract :: Args Contract where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

newtype State
  = State
  { accounts :: Accounts
  , choices :: Map ChoiceId ChosenNum
  , boundValues :: Map ValueId BigInteger
  , minSlot :: Slot
  }

derive instance genericState :: Generic State _

derive instance newtypeState :: Newtype State _

derive instance eqState :: Eq State

derive instance ordState :: Ord State

instance showState :: Show State where
  show v = genericShow v

_accounts :: Lens' State (Accounts)
_accounts = _Newtype <<< prop (SProxy :: SProxy "accounts")

_choices :: Lens' State (Map ChoiceId ChosenNum)
_choices = _Newtype <<< prop (SProxy :: SProxy "choices")

_boundValues :: Lens' State (Map ValueId BigInteger)
_boundValues = _Newtype <<< prop (SProxy :: SProxy "boundValues")

_minSlot :: Lens' State Slot
_minSlot = _Newtype <<< prop (SProxy :: SProxy "minSlot")

newtype Environment
  = Environment { slotInterval :: SlotInterval }

derive instance genericEnvironment :: Generic Environment _

derive instance newtypeEnvironment :: Newtype Environment _

derive instance eqEnvironment :: Eq Environment

derive instance ordEnvironment :: Ord Environment

instance showEnvironment :: Show Environment where
  show v = genericShow v

_slotInterval :: Lens' Environment SlotInterval
_slotInterval = _Newtype <<< prop (SProxy :: SProxy "slotInterval")

data Input
  = IDeposit AccountId Party Token BigInteger
  | IChoice ChoiceId ChosenNum
  | INotify

derive instance genericInput :: Generic Input _

derive instance eqInput :: Eq Input

derive instance ordInput :: Ord Input

instance showInput :: Show Input where
  show v = genericShow v

-- Processing of slot interval
data IntervalError
  = InvalidInterval SlotInterval
  | IntervalInPastError Slot SlotInterval

derive instance genericIntervalError :: Generic IntervalError _

derive instance eqIntervalError :: Eq IntervalError

derive instance ordIntervalError :: Ord IntervalError

instance showIntervalError :: Show IntervalError where
  show (InvalidInterval interval) = "Invalid interval: " <> show interval
  show (IntervalInPastError slot interval) = "Interval is in the past, the current slot is " <> show slot <> " but the interval is " <> show interval

data IntervalResult
  = IntervalTrimmed Environment State
  | IntervalError IntervalError

derive instance genericIntervalResult :: Generic IntervalResult _

derive instance eqIntervalResult :: Eq IntervalResult

derive instance ordIntervalResult :: Ord IntervalResult

instance showIntervalResult :: Show IntervalResult where
  show v = genericShow v

data Payment
  = Payment Party Money

derive instance genericPayment :: Generic Payment _

derive instance eqPayment :: Eq Payment

instance showPayment :: Show Payment where
  show = genericShow

data ReduceEffect
  = ReduceWithPayment Payment
  | ReduceNoPayment

derive instance genericReduceEffect :: Generic ReduceEffect _

derive instance eqReduceEffect :: Eq ReduceEffect

instance showReduceEffect :: Show ReduceEffect where
  show = genericShow

data ReduceWarning
  = ReduceNoWarning
  | ReduceNonPositivePay AccountId Payee Token BigInteger
  ---------------------- v src v dest v paid v expected
  | ReducePartialPay AccountId Payee Token BigInteger BigInteger
  -------------------------- v oldVal  v newVal
  | ReduceShadowing ValueId BigInteger BigInteger

derive instance genericReduceWarning :: Generic ReduceWarning _

derive instance eqReduceWarning :: Eq ReduceWarning

derive instance ordReduceWarning :: Ord ReduceWarning

instance showReduceWarning :: Show ReduceWarning where
  show = genericShow

data ReduceStepResult
  = Reduced ReduceWarning ReduceEffect State Contract
  | NotReduced
  | AmbiguousSlotIntervalReductionError

derive instance genericReduceStepResult :: Generic ReduceStepResult _

derive instance eqReduceStepResult :: Eq ReduceStepResult

instance showReduceStepResult :: Show ReduceStepResult where
  show = genericShow

data ReduceResult
  = ContractQuiescent (List ReduceWarning) (List Payment) State Contract
  | RRAmbiguousSlotIntervalError

derive instance genericReduceResult :: Generic ReduceResult _

derive instance eqReduceResult :: Eq ReduceResult

instance showReduceResult :: Show ReduceResult where
  show = genericShow

data ApplyWarning
  = ApplyNoWarning
  | ApplyNonPositiveDeposit Party AccountId Token BigInteger

derive instance genericApplyWarning :: Generic ApplyWarning _

derive instance eqApplyWarning :: Eq ApplyWarning

derive instance ordApplyWarning :: Ord ApplyWarning

instance showApplyWarning :: Show ApplyWarning where
  show = genericShow

data ApplyResult
  = Applied ApplyWarning State Contract
  | ApplyNoMatchError

derive instance genericApplyResult :: Generic ApplyResult _

derive instance eqApplyResult :: Eq ApplyResult

derive instance ordApplyResult :: Ord ApplyResult

instance showApplyResult :: Show ApplyResult where
  show = genericShow

data ApplyAllResult
  = ApplyAllSuccess (List TransactionWarning) (List Payment) State Contract
  | ApplyAllNoMatchError
  | ApplyAllAmbiguousSlotIntervalError

derive instance genericApplyAllResult :: Generic ApplyAllResult _

derive instance eqApplyAllResult :: Eq ApplyAllResult

instance showApplyAllResult :: Show ApplyAllResult where
  show = genericShow

data TransactionWarning
  = TransactionNonPositiveDeposit Party AccountId Token BigInteger
  | TransactionNonPositivePay AccountId Payee Token BigInteger
  | TransactionPartialPay AccountId Payee Token BigInteger BigInteger
  -- ^ src    ^ dest ^ paid ^ expected
  | TransactionShadowing ValueId BigInteger BigInteger

-- oldVal ^  newVal ^
derive instance genericTransactionWarning :: Generic TransactionWarning _

derive instance eqTransactionWarning :: Eq TransactionWarning

derive instance ordTransactionWarning :: Ord TransactionWarning

instance showTransactionWarning :: Show TransactionWarning where
  show = genericShow

-- | Transaction error
data TransactionError
  = TEAmbiguousSlotIntervalError
  | TEApplyNoMatchError
  | TEIntervalError IntervalError
  | TEUselessTransaction

derive instance genericTransactionError :: Generic TransactionError _

derive instance eqTransactionError :: Eq TransactionError

derive instance ordTransactionError :: Ord TransactionError

instance showTransactionError :: Show TransactionError where
  show TEAmbiguousSlotIntervalError = "Abiguous slot interval"
  show TEApplyNoMatchError = "At least one of the inputs in the transaction is not allowed by the contract"
  show (TEIntervalError err) = show err
  show TEUselessTransaction = "Useless Transaction"

newtype TransactionInput
  = TransactionInput
  { interval :: SlotInterval
  , inputs :: (List Input)
  }

derive instance genericTransactionInput :: Generic TransactionInput _

derive instance newtypeTransactionInput :: Newtype TransactionInput _

derive instance eqTransactionInput :: Eq TransactionInput

derive instance ordTransactionInput :: Ord TransactionInput

instance showTransactionInput :: Show TransactionInput where
  show = genericShow

data TransactionOutput
  = TransactionOutput
    { txOutWarnings :: List TransactionWarning
    , txOutPayments :: List Payment
    , txOutState :: State
    , txOutContract :: Contract
    }
  | Error TransactionError

derive instance genericTransactionOutput :: Generic TransactionOutput _

derive instance eqTransactionOutput :: Eq TransactionOutput

instance showTransactionOutput :: Show TransactionOutput where
  show = genericShow

emptyState :: Slot -> State
emptyState sn =
  State
    { accounts: mempty
    , choices: mempty
    , boundValues: mempty
    , minSlot: sn
    }

accountOwner :: AccountId -> Party
accountOwner (AccountId _ owner) = owner

inBounds :: ChosenNum -> Array Bound -> Boolean
inBounds num = any (\(Bound l u) -> num >= l && num <= u)

boundFrom :: Bound -> BigInteger
boundFrom (Bound from _) = from

boundTo :: Bound -> BigInteger
boundTo (Bound _ to) = to

-- Note: We use guards here because currently nested ifs break purty formatting
--       We need to upgrade purty and purescript to fix
fixInterval :: SlotInterval -> State -> IntervalResult
fixInterval interval@(SlotInterval from to) (State state)
  | (not <<< validInterval) interval = IntervalError (InvalidInterval interval)
  | state.minSlot `above` interval = IntervalError (IntervalInPastError state.minSlot interval)
  | otherwise =
    let
      -- newLow is both new "low" and new "minSlot" (the lower bound for slotNum)
      newLow = max from state.minSlot

      -- We know high is greater or equal than newLow (prove)
      currentInterval = SlotInterval newLow to

      env = Environment { slotInterval: currentInterval }

      newState = State (state { minSlot = newLow })
    in
      IntervalTrimmed env newState

-- EVALUATION
-- | Evaluate a @Value@ to Integer
evalValue :: Environment -> State -> Value -> BigInteger
evalValue env state value =
  let
    eval = evalValue env state
  in
    case value of
      AvailableMoney accId token -> moneyInAccount accId token (unwrap state).accounts
      Constant integer -> integer
      NegValue val -> negate (eval val)
      AddValue lhs rhs -> eval lhs + eval rhs
      SubValue lhs rhs -> eval lhs - eval rhs
      Scale (Rational num denom) rhs ->
        let
          -- quotient and reminder
          multiplied = num * eval rhs

          q = multiplied `quot` denom

          r = multiplied `rem` denom

          -- abs (rem (num/denom)) - 1/2
          abs a = if a >= zero then a else negate a

          signum x = if x > zero then 1 else if x == zero then 0 else -1

          sign = signum (fromInt 2 * abs r - abs denom)

          m = if r < zero then q - one else q + one

          isEven = (q `rem` fromInt 2) == zero
        in
          if r == zero || sign == (-1) || (sign == 0 && isEven) then q else m
      ChoiceValue choiceId defVal -> fromMaybe (eval defVal) $ Map.lookup choiceId (unwrap state).choices
      SlotIntervalStart -> view (_slotInterval <<< to ivFrom <<< to unwrap) env
      SlotIntervalEnd -> view (_slotInterval <<< to ivTo <<< to unwrap) env
      UseValue valId -> fromMaybe zero $ Map.lookup valId (unwrap state).boundValues

-- | Evaluate an @Observation@ to Bool
evalObservation :: Environment -> State -> Observation -> Boolean
evalObservation env state obs =
  let
    evalObs = evalObservation env state

    evalVal = evalValue env state
  in
    case obs of
      AndObs lhs rhs -> evalObs lhs && evalObs rhs
      OrObs lhs rhs -> evalObs lhs || evalObs rhs
      NotObs subObs -> not (evalObs subObs)
      ChoseSomething choiceId -> choiceId `Map.member` (unwrap state).choices
      ValueGE lhs rhs -> evalVal lhs >= evalVal rhs
      ValueGT lhs rhs -> evalVal lhs > evalVal rhs
      ValueLT lhs rhs -> evalVal lhs < evalVal rhs
      ValueLE lhs rhs -> evalVal lhs <= evalVal rhs
      ValueEQ lhs rhs -> evalVal lhs == evalVal rhs
      TrueObs -> true
      FalseObs -> false

asset :: CurrencySymbol -> TokenName -> BigInteger -> Assets
asset cur tok balance = Assets (Map.singleton cur (Map.singleton tok balance))

-- | Pick the first account with money in it
refundOne :: Accounts -> Maybe (Tuple (Tuple Party Money) Accounts)
refundOne accounts = case Map.toUnfoldable accounts of
  Nil -> Nothing
  Tuple (Tuple accId (Token cur tok)) balance : rest ->
    if balance > zero then
      Just (Tuple (Tuple (accountOwner accId) (asset cur tok balance)) (Map.fromFoldable rest))
    else
      refundOne (Map.fromFoldable rest)

-- | Obtains the amount of money available an account
moneyInAccount :: AccountId -> Token -> Accounts -> BigInteger
moneyInAccount accId token accounts = fromMaybe zero (Map.lookup (Tuple accId token) accounts)

-- | Sets the amount of money available in an account
updateMoneyInAccount :: AccountId -> Token -> BigInteger -> Accounts -> Accounts
updateMoneyInAccount accId token amount = if amount <= zero then Map.delete (Tuple accId token) else Map.insert (Tuple accId token) amount

{-| Add the given amount of money to an account (only if it is positive).
    Return the updated Map
-}
addMoneyToAccount :: AccountId -> Token -> BigInteger -> Accounts -> Accounts
addMoneyToAccount accId token amount accounts =
  let
    balance = moneyInAccount accId token accounts

    newBalance = balance + amount
  in
    if amount <= zero then
      accounts
    else
      updateMoneyInAccount accId token newBalance accounts

{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Payee -> Token -> BigInteger -> Accounts -> Tuple ReduceEffect Accounts
giveMoney payee token@(Token cur tok) amount accounts = case payee of
  Party party -> Tuple (ReduceWithPayment (Payment party (asset cur tok amount))) accounts
  Account accId ->
    let
      newAccs = addMoneyToAccount accId token amount accounts
    in
      Tuple ReduceNoPayment newAccs

-- | Carry a step of the contract with no inputs
reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
reduceContractStep env state contract = case contract of
  Close -> case refundOne (unwrap state).accounts of
    Just (Tuple (Tuple party money) newAccounts) ->
      let
        oldState = unwrap state

        newState = wrap (oldState { accounts = newAccounts })
      in
        Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) newState Close
    Nothing -> NotReduced
  Pay accId payee tok val cont ->
    let
      amountToPay = evalValue env state val
    in
      if amountToPay <= zero then
        let
          warning = ReduceNonPositivePay accId payee tok amountToPay
        in
          Reduced warning ReduceNoPayment state cont
      else
        let
          balance = moneyInAccount accId tok (unwrap state).accounts

          paidAmount = min balance amountToPay

          newBalance = balance - paidAmount

          newAccs = updateMoneyInAccount accId tok newBalance (unwrap state).accounts

          warning =
            if paidAmount < amountToPay then
              ReducePartialPay accId payee tok paidAmount amountToPay
            else
              ReduceNoWarning

          (Tuple payment finalAccs) = giveMoney payee tok paidAmount newAccs

          newState = wrap ((unwrap state) { accounts = finalAccs })
        in
          Reduced warning payment newState cont
  If obs cont1 cont2 ->
    let
      cont = if evalObservation env state obs then cont1 else cont2
    in
      Reduced ReduceNoWarning ReduceNoPayment state cont
  When _ timeout nextContract ->
    let
      startSlot = view (_slotInterval <<< to ivFrom) env

      endSlot = view (_slotInterval <<< to ivTo) env
    in
      if endSlot < timeout then
        NotReduced
      else
        if timeout <= startSlot then
          Reduced ReduceNoWarning ReduceNoPayment state nextContract
        else
          AmbiguousSlotIntervalReductionError
  Let valId val nextContract ->
    let
      evaluatedValue = evalValue env state val

      newState = over _boundValues (Map.insert valId evaluatedValue) state

      warn = case Map.lookup valId (unwrap state).boundValues of
        Just oldVal -> ReduceShadowing valId oldVal evaluatedValue
        Nothing -> ReduceNoWarning
    in
      Reduced warn ReduceNoPayment newState nextContract

-- | Reduce a contract until it cannot be reduced more
reduceContractUntilQuiescent :: Environment -> State -> Contract -> ReduceResult
reduceContractUntilQuiescent startEnv startState startContract =
  let
    reductionLoop ::
      Environment -> State -> Contract -> (List ReduceWarning) -> (List Payment) -> ReduceResult
    reductionLoop env state contract warnings payments = case reduceContractStep env state contract of
      Reduced warning effect newState nextContract ->
        let
          newWarnings = if warning == ReduceNoWarning then warnings else warning : warnings

          newPayments = case effect of
            ReduceWithPayment payment -> payment : payments
            ReduceNoPayment -> payments
        in
          reductionLoop env newState nextContract newWarnings newPayments
      AmbiguousSlotIntervalReductionError -> RRAmbiguousSlotIntervalError
      -- this is the last invocation of reductionLoop, so we can reverse lists
      NotReduced -> ContractQuiescent (reverse warnings) (reverse payments) state contract
  in
    reductionLoop startEnv startState startContract mempty mempty

applyCases :: Environment -> State -> Input -> List Case -> ApplyResult
applyCases env state input cases = case input, cases of
  IDeposit accId1 party1 tok1 amount, (Case (Deposit accId2 party2 tok2 val) cont) : rest ->
    if accId1 == accId2 && party1 == party2 && tok1 == tok2
      && amount
      == evalValue env state val then
      let
        warning =
          if amount > zero then
            ApplyNoWarning
          else
            ApplyNonPositiveDeposit party2 accId2 tok2 amount

        newAccounts = addMoneyToAccount accId1 tok1 amount (unwrap state).accounts

        newState = wrap ((unwrap state) { accounts = newAccounts })
      in
        Applied warning newState cont
    else
      applyCases env state input rest
  IChoice choId1 choice, (Case (Choice choId2 bounds) cont) : rest ->
    let
      newState = over _choices (Map.insert choId1 choice) state
    in
      if choId1 == choId2 && inBounds choice bounds then
        Applied ApplyNoWarning newState cont
      else
        applyCases env state input rest
  INotify, (Case (Notify obs) cont) : _
    | evalObservation env state obs -> Applied ApplyNoWarning state cont
  _, _ : rest -> applyCases env state input rest
  _, Nil -> ApplyNoMatchError

applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input (fromFoldable cases)

applyInput _ _ _ _ = ApplyNoMatchError

convertReduceWarnings :: List ReduceWarning -> List TransactionWarning
convertReduceWarnings Nil = Nil

convertReduceWarnings (first : rest) =
  ( case first of
      ReduceNoWarning -> Nil
      ReduceNonPositivePay accId payee tok amount -> (TransactionNonPositivePay accId payee tok amount) : Nil
      ReducePartialPay accId payee tok paid expected -> (TransactionPartialPay accId payee tok paid expected) : Nil
      ReduceShadowing valId oldVal newVal -> (TransactionShadowing valId oldVal newVal) : Nil
  )
    <> convertReduceWarnings rest

convertApplyWarning :: ApplyWarning -> List TransactionWarning
convertApplyWarning warn = case warn of
  ApplyNoWarning -> Nil
  ApplyNonPositiveDeposit party accId tok amount -> (TransactionNonPositiveDeposit party accId tok amount) : Nil

-- | Apply a list of Inputs to the contract
applyAllInputs :: Environment -> State -> Contract -> (List Input) -> ApplyAllResult
applyAllInputs startEnv startState startContract startInputs =
  let
    applyAllLoop ::
      Environment ->
      State ->
      Contract ->
      List Input ->
      List TransactionWarning ->
      List Payment ->
      ApplyAllResult
    applyAllLoop env state contract inputs warnings payments = case reduceContractUntilQuiescent env state contract of
      RRAmbiguousSlotIntervalError -> ApplyAllAmbiguousSlotIntervalError
      ContractQuiescent reduceWarns pays curState cont -> case inputs of
        Nil ->
          ApplyAllSuccess (warnings <> (convertReduceWarnings reduceWarns))
            (payments <> pays)
            curState
            cont
        (input : rest) -> case applyInput env curState input cont of
          Applied applyWarn newState nextContract ->
            applyAllLoop env newState nextContract rest
              ( warnings <> (convertReduceWarnings reduceWarns)
                  <> (convertApplyWarning applyWarn)
              )
              (payments <> pays)
          ApplyNoMatchError -> ApplyAllNoMatchError
  in
    applyAllLoop startEnv startState startContract startInputs mempty mempty

-- | Try to compute outputs of a transaction give its input
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract =
  let
    inputs = (unwrap tx).inputs
  in
    case fixInterval (unwrap tx).interval state of
      IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
        ApplyAllSuccess warnings payments newState cont ->
          if (contract == cont) && ((contract /= Close) || (Map.isEmpty $ (unwrap state).accounts)) then
            Error TEUselessTransaction
          else
            TransactionOutput
              { txOutWarnings: warnings
              , txOutPayments: payments
              , txOutState: newState
              , txOutContract: cont
              }
        ApplyAllNoMatchError -> Error TEApplyNoMatchError
        ApplyAllAmbiguousSlotIntervalError -> Error TEAmbiguousSlotIntervalError
      IntervalError error -> Error (TEIntervalError error)

extractRequiredActionsWithTxs :: TransactionInput -> State -> Contract -> Tuple State (Array Action)
extractRequiredActionsWithTxs txInput state contract = case computeTransaction txInput state contract of
  TransactionOutput { txOutContract, txOutState } -> Tuple txOutState (extractRequiredActions txOutContract)
  _ ->
    if not (emptyInput txInput) then
      Tuple state []
    else case fixInterval (unwrap txInput).interval state of
      IntervalTrimmed env fixState -> case reduceContractUntilQuiescent env fixState contract of
        (ContractQuiescent _ _ _ reducedContract) -> Tuple fixState (extractRequiredActions reducedContract)
        _ -> Tuple state []
      _ -> Tuple state []
  where
  emptyInput (TransactionInput { inputs }) = null inputs

extractRequiredActions :: Contract -> Array Action
extractRequiredActions contract = case contract of
  (When cases _ _) -> map (\(Case action _) -> action) cases
  _ -> mempty

moneyInContract :: State -> Money
moneyInContract state =
  foldMapWithIndex
    (\(Tuple _ (Token cur tok)) balance -> asset cur tok balance)
    (unwrap state).accounts

class HasMaxTime a where
  maxTime :: a -> Timeout

instance hasMaxTimeContract :: HasMaxTime Contract where
  maxTime Close = zero
  maxTime (Pay _ _ _ _ contract) = maxTime contract
  maxTime (If _ contractTrue contractFalse) = maxOf [ maxTime contractTrue, maxTime contractFalse ]
  maxTime (When cases timeout contract) = maxOf [ maxTime cases, timeout, maxTime contract ]
  maxTime (Let _ _ contract) = maxTime contract

instance hasMaxTimeCase :: HasMaxTime Case where
  maxTime (Case _ contract) = maxTime contract

instance hasMaxTimeArray :: HasMaxTime a => HasMaxTime (Array a) where
  maxTime = maxOf <<< map maxTime

maxOf :: Array Timeout -> Timeout
maxOf = foldl max zero
