module Marlowe.Semantics where

import Prelude
import Data.Array (foldl)
import Data.BigInteger (BigInteger)
import Data.Eq (class Eq1)
import Data.Foldable (class Foldable, any)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Generic.Rep.Show (genericShow)
import Data.Integral (class Integral)
import Data.Lens (Lens', over, set, to, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..), fromFoldable, null, reverse, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Num (class Num)
import Data.Ord (class Ord1)
import Data.Real (class Real)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Marlowe.Pretty (class Pretty, genericPretty, prettyFragment)
import Text.PrettyPrint.Leijen (appendWithSoftbreak, text)

-- We have our own Identity data type because we want a different `Show` instance
newtype IdentityF a
  = Identity a

derive instance newtypeIdentityF :: Newtype (IdentityF a) _

derive newtype instance eqIdentityF :: Eq a => Eq (IdentityF a)

derive newtype instance ordIdentityF :: Ord a => Ord (IdentityF a)

instance eq1IdentityF :: Eq1 IdentityF where
  eq1 v = eq v

instance ord1IdentityF :: Ord1 IdentityF where
  compare1 v = compare v

instance showIdentityF :: Show a => Show (IdentityF a) where
  show (Identity a) = show a

instance prettyIdentityF :: Pretty a => Pretty (IdentityF a) where
  prettyFragment (Identity a) = prettyFragment a

type PubKey
  = String

type Party
  = PubKey

type Timeout
  = Slot

type Money
  = Ada

type ChosenNum
  = BigInteger

type ChoiceName
  = String

newtype Slot
  = Slot BigInteger

derive instance genericSlot :: Generic Slot _

derive instance newtypeSlot :: Newtype Slot _

derive instance eqSlot :: Eq Slot

derive instance ordSlot :: Ord Slot

derive newtype instance showSlot :: Show Slot

derive newtype instance prettySlot :: Pretty Slot

derive newtype instance semiRingSlot :: Semiring Slot

derive newtype instance ringSlot :: Ring Slot

instance commutativeRingSlot :: CommutativeRing Slot

derive newtype instance euclideanRingSlot :: EuclideanRing Slot

derive newtype instance numSlot :: Num Slot

derive newtype instance realRingSlot :: Real Slot

derive newtype instance integralSlot :: Integral Slot

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

data AccountIdF f
  = AccountId (f BigInteger) (f PubKey)

type AccountId
  = AccountIdF IdentityF

derive instance genericAccountIdF :: Generic (AccountIdF f) _

instance eqAccountId :: (Eq (f BigInteger), Eq (f PubKey)) => Eq (AccountIdF f) where
  eq v = genericEq v

instance ordAccountId :: (Ord (f BigInteger), Ord (f PubKey)) => Ord (AccountIdF f) where
  compare v = genericCompare v

instance showAccountId :: (Show (f BigInteger), Show (f PubKey)) => Show (AccountIdF f) where
  show (AccountId number owner) = "(AccountId " <> show number <> " " <> show owner <> ")"

instance prettyAccountId :: (Show (f BigInteger), Show (f PubKey)) => Pretty (AccountIdF f) where
  prettyFragment a = text (show a)

accountOwner :: AccountId -> PubKey
accountOwner (AccountId _ owner) = unwrap owner

data ChoiceIdF f
  = ChoiceId (f String) (f PubKey)

type ChoiceId
  = ChoiceIdF IdentityF

derive instance genericChoiceIdF :: Generic (ChoiceIdF f) _

instance eqChoiceIdF :: Eq (f String) => Eq (ChoiceIdF f) where
  eq v = genericEq v

instance ordChoiceIdF :: Ord (f String) => Ord (ChoiceIdF f) where
  compare v = genericCompare v

instance showChoiceIdF :: Show (f String) => Show (ChoiceIdF f) where
  show (ChoiceId name owner) = "(ChoiceId " <> show name <> " " <> show owner <> ")"

instance prettyChoiceIdF :: Show (f String) => Pretty (ChoiceIdF f) where
  prettyFragment a = text (show a)

choiceOwner :: ChoiceId -> PubKey
choiceOwner (ChoiceId _ owner) = unwrap owner

newtype ValueIdF f
  = ValueId (f String)

type ValueId
  = ValueIdF IdentityF

derive instance genericValueIdF :: Generic (ValueIdF f) _

derive instance newtypeValueIdF :: Newtype (ValueIdF f) _

derive newtype instance eqValueIdF :: Eq (f String) => Eq (ValueIdF f)

derive newtype instance ordValueIdF :: Ord (f String) => Ord (ValueIdF f)

derive newtype instance showValueIdF :: Show (f String) => Show (ValueIdF f)

instance prettyValueId :: Show (f String) => Pretty (ValueIdF f) where
  prettyFragment a = text (show a)

data ValueF f
  = AvailableMoney (AccountIdF f)
  | Constant (f BigInteger)
  | NegValue (ValueF f)
  | AddValue (ValueF f) (ValueF f)
  | SubValue (ValueF f) (ValueF f)
  | ChoiceValue (ChoiceIdF f) (ValueF f)
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue (ValueIdF f)

type Value
  = ValueF IdentityF

derive instance genericValue :: Generic (ValueF f) _

instance eqValueF :: (Eq (f BigInteger), Eq (f String)) => Eq (ValueF f) where
  eq v = genericEq v

instance ordValueF :: (Ord (f BigInteger), Ord (f String)) => Ord (ValueF f) where
  compare v = genericCompare v

instance showValueF :: (Show (f BigInteger), Show (f String)) => Show (ValueF f) where
  show v = genericShow v

instance prettyValue :: (Pretty (f BigInteger), Show (f BigInteger), Show (f String)) => Pretty (ValueF f) where
  prettyFragment a = genericPretty a

data ObservationF f
  = AndObs (ObservationF f) (ObservationF f)
  | OrObs (ObservationF f) (ObservationF f)
  | NotObs (ObservationF f)
  | ChoseSomething (ChoiceIdF f)
  | ValueGE (ValueF f) (ValueF f)
  | ValueGT (ValueF f) (ValueF f)
  | ValueLT (ValueF f) (ValueF f)
  | ValueLE (ValueF f) (ValueF f)
  | ValueEQ (ValueF f) (ValueF f)
  | TrueObs
  | FalseObs

type Observation
  = ObservationF IdentityF

derive instance genericObservationF :: Generic (ObservationF f) _

instance eqObservationF :: (Eq (f String), Eq (f BigInteger)) => Eq (ObservationF f) where
  eq v = genericEq v

instance ordObservationF :: (Ord (f String), Ord (f BigInteger)) => Ord (ObservationF f) where
  compare v = genericCompare v

instance showObservationF :: (Show (f String), Show (f BigInteger)) => Show (ObservationF f) where
  show o = genericShow o

instance prettyObservationF :: (Show (f String), Show (f BigInteger), Pretty (f BigInteger)) => Pretty (ObservationF f) where
  prettyFragment a = genericPretty a

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
  prettyFragment a = text $ show a

inBounds :: ChosenNum -> Array Bound -> Boolean
inBounds num = any (\(Bound l u) -> num >= l && num <= u)

boundFrom :: Bound -> BigInteger
boundFrom (Bound from _) = from

boundTo :: Bound -> BigInteger
boundTo (Bound _ to) = to

data ActionF f
  = Deposit (AccountIdF f) Party (ValueF f)
  | Choice (ChoiceIdF f) (Array Bound)
  | Notify (ObservationF f)

type Action
  = ActionF IdentityF

derive instance genericActionF :: Generic (ActionF f) _

instance eqActionF :: (Eq (f String), Eq (f BigInteger)) => Eq (ActionF f) where
  eq v = genericEq v

instance ordActionF :: (Ord (f String), Ord (f BigInteger)) => Ord (ActionF f) where
  compare v = genericCompare v

instance showActionF :: (Show (f String), Show (f BigInteger)) => Show (ActionF f) where
  show (Choice cid bounds) = "(Choice " <> show cid <> " " <> show bounds <> ")"
  show v = genericShow v

instance prettyActionF :: (Show (f String), Show (f BigInteger)) => Pretty (ActionF f) where
  prettyFragment a = text (show a)

data PayeeF f
  = Account (AccountIdF f)
  | Party Party

type Payee
  = PayeeF IdentityF

derive instance genericPayeeF :: Generic (PayeeF f) _

derive instance eqPayeeF :: (Eq (f String), Eq (f BigInteger)) => Eq (PayeeF f)

derive instance ordPayeeF :: (Ord (f String), Ord (f BigInteger)) => Ord (PayeeF f)

instance showPayeeF :: (Show (f String), Show (f BigInteger)) => Show (PayeeF f) where
  show v = genericShow v

instance prettyPayeeF :: (Show (f String), Show (f BigInteger)) => Pretty (PayeeF f) where
  prettyFragment a = genericPretty a

data CaseF f
  = Case (ActionF f) (ContractF f)

type Case
  = CaseF IdentityF

derive instance genericCaseF :: Generic (CaseF f) _

instance eqCaseF :: (Eq (f String), Eq (f BigInteger)) => Eq (CaseF f) where
  eq v = genericEq v

instance ordCaseF :: (Ord (f String), Ord (f BigInteger)) => Ord (CaseF f) where
  compare v = genericCompare v

instance showCaseF :: (Show (f String), Show (f BigInteger)) => Show (CaseF f) where
  show (Case action contract) = "Case " <> show action <> " " <> show contract

-- FIXME: pretty printing is a disaster and slooooowwwww
instance prettyCaseF :: (Show (f String), Show (f BigInteger), Pretty (f BigInteger)) => Pretty (CaseF f) where
  prettyFragment (Case action contract) = appendWithSoftbreak (text "Case " <> prettyFragment action <> text " ") (prettyFragment contract)

data ContractF f
  = Close
  | Pay (AccountIdF f) (PayeeF f) (ValueF f) (ContractF f)
  | If (ObservationF f) (ContractF f) (ContractF f)
  | When (Array (CaseF f)) Timeout (ContractF f)
  | Let (ValueIdF f) (ValueF f) (ContractF f)

type Contract
  = ContractF IdentityF

derive instance genericContract :: Generic (ContractF f) _

instance eqContract :: (Eq (f String), Eq (f BigInteger)) => Eq (ContractF f) where
  eq v = genericEq v

instance ordContract :: (Ord (f String), Ord (f BigInteger)) => Ord (ContractF f) where
  compare v = genericCompare v

instance showContract :: (Show (f String), Show (f BigInteger)) => Show (ContractF f) where
  show v = genericShow v

instance prettyContract :: (Show (f String), Show (f BigInteger), Pretty (f BigInteger)) => Pretty (ContractF f) where
  prettyFragment a = genericPretty a

newtype State
  = State
  { accounts :: Map AccountId Money
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

_accounts :: Lens' State (Map AccountId Money)
_accounts = _Newtype <<< prop (SProxy :: SProxy "accounts")

_choices :: Lens' State (Map ChoiceId ChosenNum)
_choices = _Newtype <<< prop (SProxy :: SProxy "choices")

_boundValues :: Lens' State (Map ValueId BigInteger)
_boundValues = _Newtype <<< prop (SProxy :: SProxy "boundValues")

_minSlot :: Lens' State Slot
_minSlot = _Newtype <<< prop (SProxy :: SProxy "minSlot")

emptyState :: Slot -> State
emptyState sn =
  State
    { accounts: mempty
    , choices: mempty
    , boundValues: mempty
    , minSlot: sn
    }

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

data InputF f
  = IDeposit (AccountIdF f) Party Money
  | IChoice (ChoiceIdF f) ChosenNum
  | INotify

type Input
  = InputF IdentityF

derive instance genericInput :: Generic (InputF f) _

instance eqInputF :: (Eq (f String), Eq (f BigInteger)) => Eq (InputF f) where
  eq v = genericEq v

instance ordInputF :: (Ord (f String), Ord (f BigInteger)) => Ord (InputF f) where
  compare v = genericCompare v

instance showInputF :: (Show (f String), Show (f BigInteger)) => Show (InputF f) where
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
      AvailableMoney accId ->
        let
          balance = fromMaybe zero $ Map.lookup accId (unwrap state).accounts
        in
          unwrap balance
      Constant integer -> unwrap integer
      NegValue val -> negate (eval val)
      AddValue lhs rhs -> eval lhs + eval rhs
      SubValue lhs rhs -> eval lhs - eval rhs
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

-- | Pick the first account with money in it
refundOne :: Map AccountId Money -> Maybe (Tuple (Tuple Party Money) (Map AccountId Money))
refundOne accounts = do
  { key, value } <- Map.findMin accounts
  let
    rest = Map.delete key accounts
  if value > zero then pure (Tuple (Tuple (accountOwner key) value) rest) else refundOne rest

data Payment
  = Payment Party Money

derive instance genericPayment :: Generic Payment _

derive instance eqPayment :: Eq Payment

derive instance ordPayment :: Ord Payment

instance showPayment :: Show Payment where
  show = genericShow

data ReduceEffect
  = ReduceWithPayment Payment
  | ReduceNoPayment

derive instance genericReduceEffect :: Generic ReduceEffect _

derive instance eqReduceEffect :: Eq ReduceEffect

derive instance ordReduceEffect :: Ord ReduceEffect

instance showReduceEffect :: Show ReduceEffect where
  show = genericShow

-- | Obtains the amount of money available an account
moneyInAccount :: AccountId -> Map AccountId Money -> Money
moneyInAccount accId accounts = fromMaybe zero (Map.lookup accId accounts)

{-| Add the given amount of money to an account (only if it is positive).
    Return the updated Map
-}
addMoneyToAccount :: AccountId -> Money -> Map AccountId Money -> Map AccountId Money
addMoneyToAccount accId money accounts =
  let
    balance = moneyInAccount accId accounts

    newBalance = balance + money
  in
    if money <= zero then
      accounts
    else
      Map.insert accId newBalance accounts

{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Payee -> Money -> Map AccountId Money -> Tuple ReduceEffect (Map AccountId Money)
giveMoney payee money accounts = case payee of
  Party party -> Tuple (ReduceWithPayment (Payment party money)) accounts
  Account accId ->
    let
      newAccs = addMoneyToAccount accId money accounts
    in
      Tuple ReduceNoPayment newAccs

data ReduceWarning
  = ReduceNoWarning
  | ReduceNonPositivePay AccountId Payee Money
  ---------------------- v src v dest v paid v expected
  | ReducePartialPay AccountId Payee Money Money
  -------------------------- v oldVal  v newVal
  | ReduceShadowing ValueId BigInteger BigInteger

derive instance genericReduceWarning :: Generic ReduceWarning _

derive instance eqReduceWarning :: Eq ReduceWarning

derive instance ordReduceWarning :: Ord ReduceWarning

instance showReduceWarning :: Show ReduceWarning where
  show v = genericShow v

data ReduceStepResult
  = Reduced ReduceWarning ReduceEffect State Contract
  | NotReduced
  | AmbiguousSlotIntervalReductionError

derive instance genericReduceStepResult :: Generic ReduceStepResult _

derive instance eqReduceStepResult :: Eq ReduceStepResult

derive instance ordReduceStepResult :: Ord ReduceStepResult

instance showReduceStepResult :: Show ReduceStepResult where
  show = genericShow

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
  Pay accId payee val nextContract ->
    let
      moneyToPay = Lovelace (evalValue env state val)
    in
      if moneyToPay <= zero then
        Reduced (ReduceNonPositivePay accId payee moneyToPay) ReduceNoPayment state nextContract
      else
        let
          balance = moneyInAccount accId (unwrap state).accounts -- always positive

          paidMoney = min balance moneyToPay -- always positive

          newBalance = balance - paidMoney -- always positive

          newAccounts = Map.insert accId newBalance (unwrap state).accounts

          warning = if paidMoney < moneyToPay then ReducePartialPay accId payee paidMoney moneyToPay else ReduceNoWarning

          (Tuple payment finalAccounts) = giveMoney payee paidMoney newAccounts

          newState = set _accounts finalAccounts state
        in
          Reduced warning payment newState nextContract
  If observation contract1 contract2 ->
    let
      nextContract = if evalObservation env state observation then contract1 else contract2
    in
      Reduced ReduceNoWarning ReduceNoPayment state nextContract
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

data ReduceResult
  = ContractQuiescent (List ReduceWarning) (List Payment) State Contract
  | RRAmbiguousSlotIntervalError

derive instance genericReduceResult :: Generic ReduceResult _

derive instance eqReduceResult :: Eq ReduceResult

derive instance ordReduceResult :: Ord ReduceResult

instance showReduceResult :: Show ReduceResult where
  show = genericShow

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

data ApplyWarning
  = ApplyNoWarning
  | ApplyNonPositiveDeposit Party AccountId Money

derive instance genericApplyWarning :: Generic ApplyWarning _

derive instance eqApplyWarning :: Eq ApplyWarning

derive instance ordApplyWarning :: Ord ApplyWarning

instance showApplyWarning :: Show ApplyWarning where
  show v = genericShow v

data ApplyResult
  = Applied ApplyWarning State Contract
  | ApplyNoMatchError

derive instance genericApplyResult :: Generic ApplyResult _

derive instance eqApplyResult :: Eq ApplyResult

derive instance ordApplyResult :: Ord ApplyResult

instance showApplyResult :: Show ApplyResult where
  show = genericShow

applyCases :: Environment -> State -> Input -> List Case -> ApplyResult
applyCases env state input cases = case input, cases of
  IDeposit accId1 party1 money, ((Case (Deposit accId2 party2 val) cont) : rest) ->
    let
      amount = evalValue env state val

      warning =
        if amount > zero then
          ApplyNoWarning
        else
          ApplyNonPositiveDeposit party1 accId2 (Lovelace amount)

      newState = over _accounts (addMoneyToAccount accId1 money) state
    in
      if accId1 == accId2 && party1 == party2 && unwrap money == amount then
        Applied warning newState cont
      else
        applyCases env state input rest
  IChoice choId1 choice, ((Case (Choice choId2 bounds) cont) : rest) ->
    let
      newState = over _choices (Map.insert choId1 choice) state
    in
      if choId1 == choId2 && inBounds choice bounds then
        Applied ApplyNoWarning newState cont
      else
        applyCases env state input rest
  INotify, ((Case (Notify obs) cont) : _)
    | evalObservation env state obs -> Applied ApplyNoWarning state cont
  _, (_ : rest) -> applyCases env state input rest
  _, Nil -> ApplyNoMatchError

applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input (fromFoldable cases)

applyInput _ _ _ _ = ApplyNoMatchError

data TransactionWarning
  = TransactionNonPositiveDeposit Party AccountId Money
  | TransactionNonPositivePay AccountId Payee Money
  | TransactionPartialPay AccountId Payee Money Money
  -- ^ src    ^ dest ^ paid ^ expected
  | TransactionShadowing ValueId BigInteger BigInteger

-- oldVal ^  newVal ^
derive instance genericTransactionWarning :: Generic TransactionWarning _

derive instance eqTransactionWarning :: Eq TransactionWarning

derive instance ordTransactionWarning :: Ord TransactionWarning

instance showTransactionWarning :: Show TransactionWarning where
  show v = genericShow v

convertReduceWarnings :: List ReduceWarning -> List TransactionWarning
convertReduceWarnings Nil = Nil

convertReduceWarnings (first : rest) =
  ( case first of
      ReduceNoWarning -> Nil
      ReduceNonPositivePay accId payee amount -> (TransactionNonPositivePay accId payee amount) : Nil
      ReducePartialPay accId payee paid expected -> (TransactionPartialPay accId payee paid expected) : Nil
      ReduceShadowing valId oldVal newVal -> (TransactionShadowing valId oldVal newVal) : Nil
  )
    <> convertReduceWarnings rest

convertApplyWarning :: ApplyWarning -> List TransactionWarning
convertApplyWarning warn = case warn of
  ApplyNoWarning -> Nil
  ApplyNonPositiveDeposit party accId amount -> (TransactionNonPositiveDeposit party accId amount) : Nil

data ApplyAllResult
  = ApplyAllSuccess (List TransactionWarning) (List Payment) State Contract
  | ApplyAllNoMatchError
  | ApplyAllAmbiguousSlotIntervalError

derive instance genericApplyAllResult :: Generic ApplyAllResult _

derive instance eqApplyAllResult :: Eq ApplyAllResult

derive instance ordApplyAllResult :: Ord ApplyAllResult

instance showApplyAllResult :: Show ApplyAllResult where
  show = genericShow

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

-- Transactions
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

derive instance ordTransactionOutput :: Ord TransactionOutput

instance showTransactionOutput :: Show TransactionOutput where
  show = genericShow

newtype TransactionInputF f
  = TransactionInput
  { interval :: SlotInterval
  , inputs :: (List (InputF f))
  }

type TransactionInput
  = TransactionInputF IdentityF

derive instance genericTransactionInputF :: Generic (TransactionInputF f) _

derive instance newtypeTransactionInputF :: Newtype (TransactionInputF f) _

derive newtype instance eqTransactionInputF :: (Eq (f String), Eq (f BigInteger)) => Eq (TransactionInputF f)

derive newtype instance ordTransactionInputF :: (Ord (f String), Ord (f BigInteger)) => Ord (TransactionInputF f)

derive newtype instance showTransactionInputF :: (Show (f String), Show (f BigInteger)) => Show (TransactionInputF f)

-- | Try to compute outputs of a transaction give its input
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract =
  let
    inputs = (unwrap tx).inputs
  in
    case fixInterval (unwrap tx).interval state of
      IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
        ApplyAllSuccess warnings payments newState cont -> case contract == cont of -- purty breaks with `if` until we upgrade to PS 0.13
          true -> Error TEUselessTransaction
          false ->
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
moneyInContract state = foldl (+) zero $ Map.values (unwrap state).accounts
