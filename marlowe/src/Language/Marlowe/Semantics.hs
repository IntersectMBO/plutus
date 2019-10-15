{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-orphans #-}
module Language.Marlowe.Semantics where

import           Data.Map.Strict         (Map)
import qualified Data.Map.Strict         as Map
import           Data.Text               (Text)
import qualified Data.Text               as T
import           GHC.Generics            (Generic)
import           Language.Marlowe.Pretty (Pretty, prettyFragment)
import           Text.PrettyPrint.Leijen (text)

newtype Slot = Slot { getSlot :: Integer }
  deriving stock (Eq,Ord,Generic)
  deriving newtype (Pretty)

instance Show Slot where
  showsPrec p (Slot n) = showsPrec p n
instance Read Slot where
  readsPrec p x = [(Slot v, s) | (v, s) <- readsPrec p x]

instance Num Slot where
    Slot l + Slot r = Slot (l + r)
    Slot l * Slot r = Slot (l * r)
    abs (Slot l) = Slot (abs l)
    signum (Slot l) = Slot (signum l)
    fromInteger = Slot
    negate (Slot l) = Slot (negate l)

newtype Ada = Lovelace { getLovelace :: Integer }
  deriving stock (Eq,Ord,Generic)
  deriving anyclass Pretty

instance Show Ada where
    showsPrec p (Lovelace n) = showsPrec p n
instance Read Ada where
    readsPrec p x = [(Lovelace v, s) | (v, s) <- readsPrec p x]

instance Num Ada where
    Lovelace l + Lovelace r = Lovelace (l + r)
    Lovelace l * Lovelace r = Lovelace (l * r)
    abs (Lovelace l) = Lovelace (abs l)
    signum (Lovelace l) = Lovelace (signum l)
    fromInteger = Lovelace
    negate (Lovelace l) = Lovelace (negate l)

newtype PubKey = PubKey Text
  deriving (Eq,Ord)

instance Pretty PubKey where
  prettyFragment = text . show

instance Show PubKey where
  showsPrec p (PubKey txt) = showsPrec p (T.unpack txt)
instance Read PubKey where
  readsPrec p x = [(PubKey (T.pack v), s) | (v, s) <- readsPrec p x]

type Party = PubKey
type ChoiceName = Text     -- Needs to be updated in playground.
type NumAccount = Integer
type Timeout = Slot
type Money = Ada
type ChosenNum = Integer

data AccountId = AccountId NumAccount Party
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party

data ChoiceId = ChoiceId ChoiceName Party
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

newtype ValueId = ValueId Text
  deriving stock (Eq,Ord,Generic)

instance Pretty ValueId where
  prettyFragment = text . show

instance Show ValueId where
  showsPrec p (ValueId txt) = showsPrec p (T.unpack txt)
instance Read ValueId where
  readsPrec p x = [(ValueId (T.pack v), s) | (v, s) <- readsPrec p x]

data Value = AvailableMoney AccountId
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | ChoiceValue ChoiceId Value
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue ValueId
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Observation = AndObs Observation Observation
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
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data SlotInterval = SlotInterval Slot Slot
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

ivFrom, ivTo :: SlotInterval -> Slot

ivFrom (SlotInterval from _) = from
ivTo   (SlotInterval _ to)   = to

data Bound = Bound Integer Integer
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(Bound l u) -> num >= l && num <= u)

data Action = Deposit AccountId Party Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Payee = Account AccountId
           | Party Party
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Case = Case Action Contract
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data Contract = Close
              | Pay AccountId Payee Value Contract
              | If Observation Contract Contract
              | When [Case] Timeout Contract
              | Let ValueId Value Contract
  deriving (Eq,Ord,Show,Read,Generic,Pretty)

data State = State { accounts    :: Map AccountId Money
                   , choices     :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minSlot     :: Slot }
  deriving (Eq,Ord,Show,Read)

emptyState :: Slot -> State
emptyState sn = State { accounts = Map.empty
                      , choices = Map.empty
                      , boundValues = Map.empty
                      , minSlot = sn }

newtype Environment = Environment { slotInterval :: SlotInterval }
  deriving (Eq,Ord,Show,Read)

data Input = IDeposit AccountId Party Money
           | IChoice ChoiceId ChosenNum
           | INotify
  deriving (Eq,Ord,Show,Read)


-- Processing of slot interval
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError Slot SlotInterval
  deriving (Eq,Ord,Show,Read)

data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving (Eq,Ord,Show,Read)


fixInterval :: SlotInterval -> State -> IntervalResult
fixInterval interval state = let
    SlotInterval low high  = interval
    curMinSlot = minSlot state
    -- newLow is both new "low" and new "minSlot" (the lower bound for slotNum)
    newLow = max low curMinSlot
    -- We know high is greater or equal than newLow (prove)
    curInterval = SlotInterval newLow high
    env = Environment { slotInterval = curInterval }
    newState = state { minSlot = newLow }
    in if high < low then IntervalError (InvalidInterval interval)
    else if high < curMinSlot then IntervalError (IntervalInPastError curMinSlot interval)
    else IntervalTrimmed env newState

-- EVALUATION

-- | Evaluate a @Value@ to Integer
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = let
    eval = evalValue env state
    in case value of
        AvailableMoney accId -> let
            balance = Map.findWithDefault (Lovelace 0) accId (accounts state)
            in getLovelace balance
        Constant integer     -> integer
        NegValue val         -> negate (eval val)
        AddValue lhs rhs     -> eval lhs + eval rhs
        SubValue lhs rhs     -> eval lhs - eval rhs
        ChoiceValue choiceId defVal ->
            Map.findWithDefault (eval defVal) choiceId (choices state)
        SlotIntervalStart    -> (getSlot . ivFrom . slotInterval) env
        SlotIntervalEnd      -> (getSlot . ivTo . slotInterval) env
        UseValue valId       -> Map.findWithDefault 0 valId (boundValues state)


-- | Evaluate an @Observation@ to Bool
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = let
    evalObs = evalObservation env state
    evalVal = evalValue env state
    in case obs of
        AndObs lhs rhs          -> evalObs lhs && evalObs rhs
        OrObs lhs rhs           -> evalObs lhs || evalObs rhs
        NotObs subObs           -> not (evalObs subObs)
        ChoseSomething choiceId -> choiceId `Map.member` choices state
        ValueGE lhs rhs         -> evalVal lhs >= evalVal rhs
        ValueGT lhs rhs         -> evalVal lhs > evalVal rhs
        ValueLT lhs rhs         -> evalVal lhs < evalVal rhs
        ValueLE lhs rhs         -> evalVal lhs <= evalVal rhs
        ValueEQ lhs rhs         -> evalVal lhs == evalVal rhs
        TrueObs                 -> True
        FalseObs                -> False


-- | Pick the first account with money in it
refundOne :: Map AccountId Money -> Maybe ((Party, Money), Map AccountId Money)
refundOne accounts = do
    ((accId, money), rest) <- Map.minViewWithKey accounts
    if getLovelace money > 0
    then return ((accountOwner accId, money), rest)
    else refundOne rest


data Payment = Payment Party Money
  deriving (Eq,Ord,Show,Read)

data ReduceEffect = ReduceWithPayment Payment
                  | ReduceNoPayment
  deriving (Eq,Ord,Show,Read)


-- | Obtains the amount of money available an account
moneyInAccount :: AccountId -> Map AccountId Money -> Money
moneyInAccount = Map.findWithDefault (Lovelace 0)


-- | Sets the amount of money available in an account
updateMoneyInAccount :: AccountId -> Money -> Map AccountId Money -> Map AccountId Money
updateMoneyInAccount accId money =
    if getLovelace money <= 0 then Map.delete accId else Map.insert accId money


{-| Add the given amount of money to an account (only if it is positive).
    Return the updated Map
-}
addMoneyToAccount :: AccountId -> Money -> Map AccountId Money -> Map AccountId Money
addMoneyToAccount accId money accounts = let
    balance = moneyInAccount accId accounts
    newBalance = balance + money
    in if getLovelace money <= 0 then accounts
    else updateMoneyInAccount accId newBalance accounts


{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Payee -> Money -> Map AccountId Money -> (ReduceEffect, Map AccountId Money)
giveMoney payee money accounts = case payee of
    Party party   -> (ReduceWithPayment (Payment party money), accounts)
    Account accId -> let
        newAccs = addMoneyToAccount accId money accounts
        in (ReduceNoPayment, newAccs)

-- REDUCE

data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay AccountId Payee Integer
                   | ReducePartialPay AccountId Payee Money Money
                                    -- ^ src    ^ dest ^ paid ^ expected
                   | ReduceShadowing ValueId Integer Integer
                                     -- oldVal ^  newVal ^
  deriving (Eq,Ord,Show,Read)


data ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                      | NotReduced
                      | AmbiguousSlotIntervalReductionError
  deriving (Eq,Ord,Show,Read)


-- | Carry a step of the contract with no inputs
reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
reduceContractStep env state contract = case contract of

    Close -> case refundOne (accounts state) of
        Just ((party, money), newAccounts) -> let
            newState = state { accounts = newAccounts }
            in Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) newState Close
        Nothing -> NotReduced

    Pay accId payee val cont -> let
        amountToPay = evalValue env state val
        in  if amountToPay <= 0
            then Reduced (ReduceNonPositivePay accId payee amountToPay) ReduceNoPayment state cont
            else let
                balance    = moneyInAccount accId (accounts state) -- always positive
                moneyToPay = Lovelace amountToPay -- always positive
                paidMoney  = min balance moneyToPay -- always positive
                newBalance = balance - paidMoney -- always positive
                newAccs    = updateMoneyInAccount accId newBalance (accounts state)
                warning = if paidMoney < moneyToPay
                          then ReducePartialPay accId payee paidMoney moneyToPay
                          else ReduceNoWarning
                (payment, finalAccs) = giveMoney payee paidMoney newAccs
                in Reduced warning payment (state { accounts = finalAccs }) cont

    If obs cont1 cont2 -> let
        cont = if evalObservation env state obs then cont1 else cont2
        in Reduced ReduceNoWarning ReduceNoPayment state cont

    When _ timeout cont -> let
        startSlot = ivFrom (slotInterval env)
        endSlot   = ivTo (slotInterval env)
        -- if timeout in future – do not reduce
        in if endSlot < timeout then NotReduced
        -- if timeout in the past – reduce to timeout continuation
        else if timeout <= startSlot then Reduced ReduceNoWarning ReduceNoPayment state cont
        -- if timeout in the slot range – issue an ambiguity error
        else AmbiguousSlotIntervalReductionError

    Let valId val cont -> let
        evaluatedValue = evalValue env state val
        boundVals = boundValues state
        newState = state { boundValues = Map.insert valId evaluatedValue boundVals }
        warn = case Map.lookup valId boundVals of
              Just oldVal -> ReduceShadowing valId oldVal evaluatedValue
              Nothing     -> ReduceNoWarning
        in Reduced warn ReduceNoPayment newState cont


data ReduceResult = ContractQuiescent [ReduceWarning] [Payment] State Contract
                  | RRAmbiguousSlotIntervalError
  deriving (Eq,Ord,Show,Read)

-- | Reduce a contract until it cannot be reduced more
reduceContractUntilQuiescent :: Environment -> State -> Contract -> ReduceResult
reduceContractUntilQuiescent env state contract = let
    reductionLoop
      :: Environment -> State -> Contract -> [ReduceWarning] -> [Payment] -> ReduceResult
    reductionLoop env state contract warnings payments =
        case reduceContractStep env state contract of
            Reduced warning effect newState cont -> let
                newWarnings = if warning == ReduceNoWarning then warnings
                              else warning : warnings
                newPayments  = case effect of
                    ReduceWithPayment payment -> payment : payments
                    ReduceNoPayment           -> payments
                in reductionLoop env newState cont newWarnings newPayments
            AmbiguousSlotIntervalReductionError -> RRAmbiguousSlotIntervalError
            -- this is the last invocation of reductionLoop, so we can reverse lists
            NotReduced -> ContractQuiescent (reverse warnings) (reverse payments) state contract

    in reductionLoop env state contract [] []

data ApplyWarning = ApplyNoWarning
                  | ApplyNonPositiveDeposit Party AccountId Integer
  deriving (Eq,Ord,Show,Read)

data ApplyResult = Applied ApplyWarning State Contract
                 | ApplyNoMatchError
  deriving (Eq,Ord,Show,Read)

-- Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case] -> ApplyResult
applyCases env state input cases = case (input, cases) of
    (IDeposit accId1 party1 money, Case (Deposit accId2 party2 val) cont : rest) -> let
        amount = evalValue env state val
        warning = if amount > 0
                  then ApplyNoWarning
                  else ApplyNonPositiveDeposit party1 accId2 amount
        newState = state { accounts = addMoneyToAccount accId1 money (accounts state) }
        in if accId1 == accId2 && party1 == party2 && getLovelace money == amount
        then Applied warning newState cont
        else applyCases env state input rest
    (IChoice choId1 choice, Case (Choice choId2 bounds) cont : rest) -> let
        newState = state { choices = Map.insert choId1 choice (choices state) }
        in if choId1 == choId2 && inBounds choice bounds
        then Applied ApplyNoWarning newState cont
        else applyCases env state input rest
    (INotify, Case (Notify obs) cont : _) | evalObservation env state obs -> Applied ApplyNoWarning state cont
    (_, _ : rest) -> applyCases env state input rest
    (_, []) -> ApplyNoMatchError


applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input cases
applyInput _ _ _ _                          = ApplyNoMatchError

-- APPLY ALL

data TransactionWarning = TransactionNonPositiveDeposit Party AccountId Integer
                        | TransactionNonPositivePay AccountId Payee Integer
                        | TransactionPartialPay AccountId Payee Money Money
                                               -- ^ src    ^ dest ^ paid ^ expected
                        | TransactionShadowing ValueId Integer Integer
                                                -- oldVal ^  newVal ^
  deriving (Eq,Ord,Show,Read)

convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning]
convertReduceWarnings =
  foldr (\ first ->
           (++)
             (case first of
                  ReduceNoWarning -> []
                  ReduceNonPositivePay accId payee
                    amount -> [TransactionNonPositivePay accId payee amount]
                  ReducePartialPay accId payee paid
                    expected -> [TransactionPartialPay accId payee paid expected]
                  ReduceShadowing valId oldVal newVal -> [TransactionShadowing valId
                                                            oldVal
                                                            newVal])) []


convertApplyWarning :: ApplyWarning -> [TransactionWarning]
convertApplyWarning warn =
  case warn of
    ApplyNoWarning -> []
    ApplyNonPositiveDeposit party accId amount ->
           [TransactionNonPositiveDeposit party accId amount]

data ApplyAllResult = ApplyAllSuccess [TransactionWarning] [Payment] State Contract
                    | ApplyAllNoMatchError
                    | ApplyAllAmbiguousSlotIntervalError
  deriving (Eq,Ord,Show)


-- | Apply a list of Inputs to the contract
applyAllInputs :: Environment -> State -> Contract -> [Input] -> ApplyAllResult
applyAllInputs env state contract inputs = let
    applyAllLoop
        :: Environment
        -> State
        -> Contract
        -> [Input]
        -> [TransactionWarning]
        -> [Payment]
        -> ApplyAllResult
    applyAllLoop env state contract inputs warnings payments =
        case reduceContractUntilQuiescent env state contract of
            RRAmbiguousSlotIntervalError -> ApplyAllAmbiguousSlotIntervalError
            ContractQuiescent reduceWarns pays curState cont -> case inputs of
                [] -> ApplyAllSuccess (warnings ++ convertReduceWarnings reduceWarns)
                                                   (payments ++ pays) curState cont
                (input : rest) -> case applyInput env curState input cont of
                    Applied applyWarn newState cont ->
                        applyAllLoop env newState cont rest
                                     (warnings ++ convertReduceWarnings reduceWarns
                                               ++ convertApplyWarning applyWarn)
                                     (payments ++ pays)
                    ApplyNoMatchError -> ApplyAllNoMatchError
    in applyAllLoop env state contract inputs [] []

data TransactionError = TEAmbiguousSlotIntervalError
                      | TEApplyNoMatchError
                      | TEIntervalError IntervalError
                      | TEUselessTransaction
  deriving (Eq,Ord,Show,Read)

data TransactionOutput =
    TransactionOutput
        { txOutWarnings :: [TransactionWarning]
        , txOutPayments :: [Payment]
        , txOutState    :: State
        , txOutContract :: Contract }
    | Error TransactionError
  deriving (Eq,Ord,Show,Read)

data TransactionInput = TransactionInput
    { txInterval :: SlotInterval
    , txInputs   :: [Input] }
  deriving (Eq,Ord,Show,Read)

-- | Try to compute outputs of a transaction give its input
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract = let
    inputs = txInputs tx
    in case fixInterval (txInterval tx) state of
        IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
            ApplyAllSuccess warnings payments newState cont -> let
                in  if contract == cont
                    then Error TEUselessTransaction
                    else TransactionOutput { txOutWarnings = warnings
                                           , txOutPayments = payments
                                           , txOutState = newState
                                           , txOutContract = cont }
            ApplyAllNoMatchError -> Error TEApplyNoMatchError
            ApplyAllAmbiguousSlotIntervalError -> Error TEAmbiguousSlotIntervalError
        IntervalError error -> Error (TEIntervalError error)


-- | Calculates an upper bound for the maximum lifespan of a contract
contractLifespanUpperBound :: Contract -> Integer
contractLifespanUpperBound contract = case contract of
    Close -> 0
    Pay _ _ _ cont -> contractLifespanUpperBound cont
    If _ contract1 contract2 ->
        max (contractLifespanUpperBound contract1) (contractLifespanUpperBound contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespanUpperBound cont) cases
        in maximum (getSlot timeout : contractLifespanUpperBound subContract : contractsLifespans)
    Let _ _ cont -> contractLifespanUpperBound cont

