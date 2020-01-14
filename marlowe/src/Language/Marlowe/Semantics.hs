{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
-- Big hammer, but helps
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

{-| = Marlowe: financial contracts domain specific language for blockchain

Here we present a reference implementation of Marlowe, domain-specific language targeted at
the execution of financial contracts in the style of Peyton Jones et al
on Cardano.

== Semantics

Semantics is based on <https://github.com/input-output-hk/marlowe/blob/stable/src/Semantics.hs>

Marlowe Contract execution is a chain of transactions,
where remaining contract and its state is passed through /Data Script/,
and actions (i.e. /Choices/) are passed as
/Redeemer Script/

/Validation Script/ is always the same Marlowe interpreter implementation, available below.
-}

module Language.Marlowe.Semantics where

import           GHC.Generics               (Generic)
import           Language.Marlowe.Pretty    (Pretty (..))
import           Language.PlutusTx          (makeIsData)
import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.AssocMap (Map)
import qualified Language.PlutusTx.AssocMap as Map
import           Language.PlutusTx.Lift     (makeLift)
import           Language.PlutusTx.Prelude  hiding ((<>))
import           Ledger                     (PubKey (..), Slot (..))
import           Ledger.Interval            (Extended (..), Interval (..), LowerBound (..), UpperBound (..))
import           Ledger.Scripts             (DataValue (..))
import           Ledger.Validation
import           Ledger.Value               (CurrencySymbol, TokenName)
import qualified Ledger.Value               as Val
import qualified Prelude                    as P
import           Text.PrettyPrint.Leijen    (comma, hang, lbrace, line, rbrace, space, text, (<>))

{-# ANN module ("HLint: ignore Avoid restricted function" :: String) #-}

{- Functions that used in Plutus Core must be inlineable,
   so their code is available for PlutusTx compiler -}
{-# INLINABLE accountOwner #-}
{-# INLINABLE inBounds #-}
{-# INLINABLE fixInterval #-}
{-# INLINABLE evalValue #-}
{-# INLINABLE evalObservation #-}
{-# INLINABLE refundOne #-}
{-# INLINABLE moneyInAccount #-}
{-# INLINABLE updateMoneyInAccount #-}
{-# INLINABLE addMoneyToAccount #-}
{-# INLINABLE giveMoney #-}
{-# INLINABLE reduceContractStep #-}
{-# INLINABLE reduceContractUntilQuiescent #-}
{-# INLINABLE applyCases #-}
{-# INLINABLE applyInput #-}
{-# INLINABLE convertReduceWarnings #-}
{-# INLINABLE applyAllInputs #-}
{-# INLINABLE getSignatures #-}
{-# INLINABLE checkSignatures #-}
{-# INLINABLE computeTransaction #-}
{-# INLINABLE contractLifespanUpperBound #-}
{-# INLINABLE totalBalance #-}
{-# INLINABLE validatePayments #-}
{-# INLINABLE marloweValidator #-}

-- * Aliaces

type Party = PubKey
type NumAccount = Integer
type Timeout = Slot
type Money = Val.Value
type ChoiceName = ByteString
type ChosenNum = Integer
type SlotInterval = (Slot, Slot)
type Accounts = Map (AccountId, Token) Integer
type TransactionSignatures = Map Party Bool

-- * Data Types

{-| Party account id.
    Accounts have a number NumAccount and an owner,
    who is a Party to the contract.
    @
    AccountId 0 alicePK
    AccountId 1 alicePK
    @
    Note that alicePK is the owner here in the sense that she will be
    refunded any money in the account when the contract terminates.
-}
data AccountId = AccountId NumAccount Party
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)


{-| Choices – of integers – are identified by ChoiceId
    which combines a name for the choice with the Party who had made the choice.
-}
data ChoiceId = ChoiceId ByteString Party
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)

{-| Token - represents a currency or token, it groups
    a pair of a currency symbol and token name.
-}
data Token = Token CurrencySymbol TokenName
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)

{-| Values, as defined using Let are identified by name,
    and can be used by 'UseValue' construct.
-}
newtype ValueId = ValueId ByteString
  deriving stock (Show,P.Eq,P.Ord)

{-| Values include some quantities that change with time,
    including “the slot interval”, “the current balance of an account (in Lovelace)”,
    and any choices that have already been made.

    Values can also be combined using addition, subtraction and negation.
-}
data Value = AvailableMoney AccountId Token
           | Constant Integer
           | NegValue Value
           | AddValue Value Value
           | SubValue Value Value
           | ChoiceValue ChoiceId Value
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue ValueId
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)


{-| Observations are Boolean values derived by comparing values,
    and can be combined using the standard Boolean operators.

    It is also possible to observe whether any choice has been made
    (for a particular identified choice).
-}
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
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)

data Bound = Bound Integer Integer
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)

{-| Actions happen at particular points during execution.
    Three kinds of action are possible:

    * A @Deposit n p v@ makes a deposit of value @v@ into account @n@ belonging to party @p@.

    * A choice is made for a particular id with a list of bounds on the values that are acceptable.
      For example, @[(0, 0), (3, 5]@ offers the choice of one of 0, 3, 4 and 5.

    * The contract is notified that a particular observation be made.
      Typically this would be done by one of the parties,
      or one of their wallets acting automatically.
-}
data Action = Deposit AccountId Party Token Value
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)


{-| A payment can be made to one of the parties to the contract,
    or to one of the accounts of the contract,
    and this is reflected in the definition.
-}
data Payee = Account AccountId
           | Party Party
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)

{-  Plutus doesn't support mutually recursive data types yet.
    datatype Case is mutually recurvive with @Contract@
-}
data Case a = Case Action a
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)


{-| Marlowe has five ways of building contracts.
    Four of these – 'Pay', 'Let', 'If' and 'When' –
    build a complex contract from simpler contracts, and the fifth, 'Close',
    is a simple contract.
    At each step of execution, as well as returning a new state and continuation contract,
    it is possible that effects – payments – and warnings can be generated too.
-}
data Contract = Close
              | Pay AccountId Payee Token Value Contract
              | If Observation Contract Contract
              | When [Case Contract] Timeout Contract
              | Let ValueId Value Contract
  deriving stock (Show,Read,Generic,P.Eq,P.Ord)
  deriving anyclass (Pretty)


{-| Marlowe contract internal state. Stored in a /Data Script/ of a transaction output.
-}
data State = State { accounts    :: Accounts
                   , choices     :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minSlot     :: Slot }
  deriving stock (Show)


{-| Execution environment. Contains a slot interval of a transaction.
-}
newtype Environment = Environment { slotInterval :: SlotInterval }
  deriving stock (Show,P.Eq,P.Ord)


{-| Input for a Marlowe contract. Correspond to expected 'Action's.
-}
data Input = IDeposit AccountId Party Token Integer
           | IChoice ChoiceId ChosenNum
           | INotify
  deriving stock (Show,P.Eq,Generic)
  deriving anyclass (Pretty)


{-| Slot interval errors.
    'InvalidInterval' means @slotStart > slotEnd@, and
    'IntervalInPastError' means slot interval is in the past, relative to the contract.

    These errors should never occur, but we are always prepared.
-}
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError Slot SlotInterval
  deriving stock (Show)


-- | Result of 'fixInterval'
data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving stock (Show)


{-| Payment occurs during 'Pay' contract evaluation, and
    when positive balances are payed out on contract closure.
-}
data Payment = Payment Party Money
  deriving stock (Show)


-- | Effect of 'reduceContractStep' computation
data ReduceEffect = ReduceWithPayment Payment
                  | ReduceNoPayment
  deriving stock (Show)


-- | Warning during 'reduceContractStep'
data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay AccountId Payee Token Integer
                   | ReducePartialPay AccountId Payee Token Integer Integer
                                     -- ^ src    ^ dest                           ^ paid ^ expected
                   | ReduceShadowing ValueId Integer Integer
                                    -- oldVal ^  newVal ^
  deriving stock (Show)


-- | Result of 'reduceContractStep'
data ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                      | NotReduced
                      | AmbiguousSlotIntervalReductionError
  deriving stock (Show)


-- | Result of 'reduceContractUntilQuiescent'
data ReduceResult = ContractQuiescent [ReduceWarning] [Payment] State Contract
                  | RRAmbiguousSlotIntervalError
  deriving stock (Show)


-- | Warning of 'applyCases'
data ApplyWarning = ApplyNoWarning
                  | ApplyNonPositiveDeposit Party AccountId Token Integer
  deriving stock (Show)


-- | Result of 'applyCases'
data ApplyResult = Applied ApplyWarning State Contract
                 | ApplyNoMatchError
  deriving stock (Show)


-- | Result of 'applyAllInputs'
data ApplyAllResult = ApplyAllSuccess [TransactionWarning] [Payment] State Contract
                    | ApplyAllNoMatchError
                    | ApplyAllAmbiguousSlotIntervalError
  deriving stock (Show)


-- | Warnings during transaction computation
data TransactionWarning = TransactionNonPositiveDeposit Party AccountId Token Integer
                        | TransactionNonPositivePay AccountId Payee Token Integer
                        | TransactionPartialPay AccountId Payee Token Integer Integer
                                                -- ^ src    ^ dest    ^ paid ^ expected
                        | TransactionShadowing ValueId Integer Integer
                                                -- oldVal ^  newVal ^
  deriving stock (Show, Generic)
  deriving anyclass (Pretty)


-- | Transaction error
data TransactionError = TEAmbiguousSlotIntervalError
                      | TEApplyNoMatchError
                      | TEIntervalError IntervalError
                      | TEUselessTransaction
  deriving stock (Show)


{-| Marlowe transaction input.
-}
data TransactionInput = TransactionInput
    { txInterval :: SlotInterval
    , txInputs   :: [Input] }
  deriving stock (Show)

instance Pretty TransactionInput where
    prettyFragment tInp = text "TransactionInput" <> space <> lbrace <> line <> txIntLine <> line <> txInpLine
        where
            txIntLine = hang 2 $ text "txInterval = " <> prettyFragment (txInterval tInp) <> comma
            txInpLine = hang 2 $ text "txInputs = " <> prettyFragment (txInputs tInp) <> rbrace


{-| Marlowe transaction output.
-}
data TransactionOutput =
    TransactionOutput
        { txOutWarnings :: [TransactionWarning]
        , txOutPayments :: [Payment]
        , txOutState    :: State
        , txOutContract :: Contract }
    | Error TransactionError
  deriving stock (Show)


{-|
    This data type is a content of a contract's /Data Script/
-}
data MarloweData = MarloweData {
        marloweCreator  :: Party,
        marloweState    :: State,
        marloweContract :: Contract
    } deriving stock (Show)


-- | Empty State for a given minimal 'Slot'
emptyState :: Slot -> State
emptyState sn = State
    { accounts = Map.empty ()
    , choices  = Map.empty ()
    , boundValues = Map.empty ()
    , minSlot = sn }


{-| Returns an owner of an account.
    We don't use record syntax for 'AccountId' because that
    results in cumbersome `Read`/`Show` representations.
-}
accountOwner :: AccountId -> Party
accountOwner (AccountId _ party) = party


-- | Check if a 'num' is withint a list of inclusive bounds.
inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(Bound l u) -> num >= l && num <= u)


{- Checks 'interval' and trim it if necessary. -}
fixInterval :: SlotInterval -> State -> IntervalResult
fixInterval interval state =
    case interval of
        (low, high)
          | high < low -> IntervalError (InvalidInterval interval)
          | otherwise -> let
            curMinSlot = minSlot state
            -- newLow is both new "low" and new "minSlot" (the lower bound for slotNum)
            newLow = max low curMinSlot
            -- We know high is greater or equal than newLow (prove)
            curInterval = (newLow, high)
            env = Environment { slotInterval = curInterval }
            newState = state { minSlot = newLow }
            in if high < curMinSlot then IntervalError (IntervalInPastError curMinSlot interval)
            else IntervalTrimmed env newState


{-|
  Evaluates @Value@ given current @State@ and @Environment@
-}
evalValue :: Environment -> State -> Value -> Integer
evalValue env state value = let
    eval = evalValue env state
    in case value of
        AvailableMoney accId token -> moneyInAccount accId token (accounts state)
        Constant integer     -> integer
        NegValue val         -> negate (eval val)
        AddValue lhs rhs     -> eval lhs + eval rhs
        SubValue lhs rhs     -> eval lhs - eval rhs
        ChoiceValue choiceId defVal ->
            case Map.lookup choiceId (choices state) of
                Just x  -> x
                Nothing -> eval defVal
        SlotIntervalStart    -> getSlot (fst (slotInterval env))
        SlotIntervalEnd      -> getSlot (snd (slotInterval env))
        UseValue valId       ->
            case Map.lookup valId (boundValues state) of
                Just x  -> x
                Nothing -> 0


-- | Evaluate 'Observation' to 'Bool'.
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
refundOne :: Accounts -> Maybe ((Party, Money), Accounts)
refundOne accounts = case Map.toList accounts of
    [] -> Nothing
    ((accId, Token cur tok), balance) : rest ->
        if balance > 0
        then Just ((accountOwner accId, Val.singleton cur tok balance), Map.fromList rest)
        else refundOne (Map.fromList rest)


-- | Obtains the amount of money available an account
moneyInAccount :: AccountId -> Token -> Accounts -> Integer
moneyInAccount accId token accounts = case Map.lookup (accId, token) accounts of
    Just x  -> x
    Nothing -> 0


-- | Sets the amount of money available in an account
updateMoneyInAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
updateMoneyInAccount accId token amount =
    if amount <= 0 then Map.delete (accId, token) else Map.insert (accId, token) amount


-- Add the given amount of money to an accoun (only if it is positive)
-- Return the updated Map
addMoneyToAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
addMoneyToAccount accId token amount accounts = let
    balance = moneyInAccount accId token accounts
    newBalance = balance + amount
    in if amount <= 0 then accounts
    else updateMoneyInAccount accId token newBalance accounts


{-| Gives the given amount of money to the given payee.
    Returns the appropriate effect and updated accounts
-}
giveMoney :: Payee -> Token -> Integer -> Accounts -> (ReduceEffect, Accounts)
giveMoney payee (Token cur tok) amount accounts = case payee of
    Party party   -> (ReduceWithPayment (Payment party (Val.singleton cur tok amount)), accounts)
    Account accId -> let
        newAccs = addMoneyToAccount accId (Token cur tok) amount accounts
        in (ReduceNoPayment, newAccs)


-- | Carry a step of the contract with no inputs
reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
reduceContractStep env state contract = case contract of

    Close -> case refundOne (accounts state) of
        Just ((party, money), newAccounts) -> let
            newState = state { accounts = newAccounts }
            in Reduced ReduceNoWarning (ReduceWithPayment (Payment party money)) newState Close
        Nothing -> NotReduced

    Pay accId payee tok val cont -> let
        amountToPay = evalValue env state val
        in  if amountToPay <= 0
            then let
                warning = ReduceNonPositivePay accId payee tok amountToPay
                in Reduced warning ReduceNoPayment state cont
            else let
                balance    = moneyInAccount accId tok (accounts state)
                paidAmount = min balance amountToPay
                newBalance = balance - paidAmount
                newAccs = updateMoneyInAccount accId tok newBalance (accounts state)
                warning = if paidAmount < amountToPay
                          then ReducePartialPay accId payee tok paidAmount amountToPay
                          else ReduceNoWarning
                (payment, finalAccs) = giveMoney payee tok paidAmount newAccs
                newState = state { accounts = finalAccs }
                in Reduced warning payment newState cont

    If obs cont1 cont2 -> let
        cont = if evalObservation env state obs then cont1 else cont2
        in Reduced ReduceNoWarning ReduceNoPayment state cont

    When _ timeout cont -> let
        startSlot = fst (slotInterval env)
        endSlot   = snd (slotInterval env)
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


-- | Apply a single Input to the contract (assumes the contract is reduced)
applyCases :: Environment -> State -> Input -> [Case Contract] -> ApplyResult
applyCases env state input cases = case (input, cases) of
    (IDeposit accId1 party1 tok1 amount,
        Case (Deposit accId2 party2 tok2 val) cont : rest) ->
        if accId1 == accId2 && party1 == party2 && tok1 == tok2
                && amount == evalValue env state val
        then let
            warning = if amount > 0 then ApplyNoWarning
                      else ApplyNonPositiveDeposit party2 accId2 tok2 amount
            newAccounts = addMoneyToAccount accId1 tok1 amount (accounts state)
            newState = state { accounts = newAccounts }
            in Applied warning newState cont
        else applyCases env state input rest
    (IChoice choId1 choice, Case (Choice choId2 bounds) cont : rest) ->
        if choId1 == choId2 && inBounds choice bounds
        then let
            newState = state { choices = Map.insert choId1 choice (choices state) }
            in Applied ApplyNoWarning newState cont
        else applyCases env state input rest
    (INotify, Case (Notify obs) cont : _)
        | evalObservation env state obs -> Applied ApplyNoWarning state cont
    (_, _ : rest) -> applyCases env state input rest
    (_, []) -> ApplyNoMatchError


-- | Apply a single @Input@ to a current contract
applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input cases
applyInput _ _ _ _                          = ApplyNoMatchError


-- | Propagate 'ReduceWarning' to 'TransactionWarning'
convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning]
convertReduceWarnings = foldr (\warn acc -> case warn of
    ReduceNoWarning -> acc
    ReduceNonPositivePay accId payee tok amount ->
        TransactionNonPositivePay accId payee tok amount : acc
    ReducePartialPay accId payee tok paid expected ->
        TransactionPartialPay accId payee tok paid expected : acc
    ReduceShadowing valId oldVal newVal ->
        TransactionShadowing valId oldVal newVal : acc
    ) []


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
                [] -> ApplyAllSuccess
                    (warnings ++ convertReduceWarnings reduceWarns)
                    (payments ++ pays)
                    curState
                    cont
                (input : rest) -> case applyInput env curState input cont of
                    Applied applyWarn newState cont ->
                        applyAllLoop
                            env
                            newState
                            cont
                            rest
                            (warnings
                                ++ convertReduceWarnings reduceWarns
                                ++ convertApplyWarning applyWarn)
                            (payments ++ pays)
                    ApplyNoMatchError -> ApplyAllNoMatchError
    in applyAllLoop env state contract inputs [] []
  where
    convertApplyWarning :: ApplyWarning -> [TransactionWarning]
    convertApplyWarning warn =
        case warn of
            ApplyNoWarning -> []
            ApplyNonPositiveDeposit party accId tok amount ->
                [TransactionNonPositiveDeposit party accId tok amount]


-- | Extract necessary signatures from transaction inputs
getSignatures :: [Input] -> TransactionSignatures
getSignatures = foldl addSig (Map.empty())
  where
    addSig acc (IDeposit _ p _ _)         = Map.insert p True acc
    addSig acc (IChoice (ChoiceId _ p) _) = Map.insert p True acc
    addSig acc INotify                    = acc


checkSignatures :: PendingTx -> TransactionSignatures -> Bool
checkSignatures pendingTx sigs = let
    requiredSigs = Map.keys sigs
    in all (txSignedBy pendingTx) requiredSigs


-- | Try to compute outputs of a transaction given its inputs, a contract, and it's @State@
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract = let
    inputs = txInputs tx
    in case fixInterval (txInterval tx) state of
        IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
            ApplyAllSuccess warnings payments newState cont -> let
                in  if (contract == cont) && ((contract /= Close) || (Map.null $ accounts state))
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
    Pay _ _ _ _ cont -> contractLifespanUpperBound cont
    If _ contract1 contract2 ->
        max (contractLifespanUpperBound contract1) (contractLifespanUpperBound contract2)
    When cases timeout subContract -> let
        contractsLifespans = fmap (\(Case _ cont) -> contractLifespanUpperBound cont) cases
        in maximum (getSlot timeout : contractLifespanUpperBound subContract : contractsLifespans)
    Let _ _ cont -> contractLifespanUpperBound cont


totalBalance :: Accounts -> Money
totalBalance accounts = foldMap
    (\((_, Token cur tok), balance) -> Val.singleton cur tok balance)
    (Map.toList accounts)


validatePayments :: PendingTx -> [Payment] -> Bool
validatePayments pendingTx txOutPayments = let

    collect outputs PendingTxOut{pendingTxOutValue,
        pendingTxOutType=PubKeyTxOut pubKey} = let
        newValue = case Map.lookup pubKey outputs of
            Just value -> value + pendingTxOutValue
            Nothing    -> pendingTxOutValue
        in Map.insert pubKey newValue outputs
    collect outputs _ = outputs

    collectPayments payments (Payment party money) = let
        newValue = case Map.lookup party payments of
            Just value -> value + money
            Nothing    -> money
        in Map.insert party newValue payments

    outputs = foldl collect mempty (pendingTxOutputs pendingTx)

    payments = foldl collectPayments mempty txOutPayments

    listOfPayments :: [(Party, Money)]
    listOfPayments = Map.toList payments

    checkValidPayment (party, expectedPayment) =
        case Map.lookup party outputs of
            Just value -> value `Val.geq` expectedPayment
            Nothing    -> False

    in all checkValidPayment listOfPayments


{-|
    Check that all accounts have positive balance.
 -}
validateBalances :: State -> Bool
validateBalances State{..} = all (\(_, balance) -> balance > 0) (Map.toList accounts)


{-| Ensure that 'pendingTx' contains expected payments.   -}
validateTxOutputs :: PendingTx -> Party -> TransactionOutput -> Bool
validateTxOutputs pendingTx creator expectedTxOutputs = case expectedTxOutputs of
    TransactionOutput {txOutPayments, txOutState, txOutContract} ->
        case txOutContract of
            -- if it's a last transaction, don't expect any continuation,
            -- everything is payed out.
            Close -> validatePayments pendingTx txOutPayments
            -- otherwise check the continuation
            _ -> case getContinuingOutputs pendingTx of
                    [PendingTxOut
                        { pendingTxOutType=(ScriptTxOut _ dsh)
                        , pendingTxOutValue
                        }] | Just (DataValue ds) <- findData dsh pendingTx -> case PlutusTx.fromData ds of
                            Just (MarloweData expectedCreator expectedState expectedContract) -> let
                                scriptOutputValue = pendingTxOutValue
                                validContract = expectedCreator == creator
                                    && txOutState == expectedState
                                    && txOutContract == expectedContract
                                outputBalance = totalBalance (accounts txOutState)
                                outputBalanceOk = scriptOutputValue == outputBalance
                                in  outputBalanceOk
                                    && validContract
                                    && validatePayments pendingTx txOutPayments
                            _ -> False
                    _ -> False
    Error _ -> traceErrorH "Error"


{-|
    Marlowe Interpreter Validator generator.
-}
marloweValidator
  :: PubKey -> MarloweData -> [Input] -> PendingTx -> Bool
marloweValidator creator MarloweData{..} inputs pendingTx@PendingTx{..} = let
    {-  Embed contract creator public key. This makes validator script unique,
        which makes a particular contract to have a unique script address.
        That makes it easier to watch for contract actions inside a wallet. -}

    checkCreator =
        marloweCreator == creator || traceErrorH "Wrong contract creator"

    {-  We require Marlowe Tx to have both lower bound and upper bounds in 'SlotRange'.
        All are inclusive.
    -}
    (minSlot, maxSlot) = case pendingTxValidRange of
        Interval (LowerBound (Finite l) True) (UpperBound (Finite h) True) -> (l, h)
        _ -> traceErrorH "Tx valid slot must have lower bound and upper bounds"

    positiveBalances = validateBalances marloweState ||
        traceErrorH "Invalid contract state. There exists an account with non positive balance"

    {-  We do not check that a transaction contains exact input payments.
        We only require a signature of a party.
        This gives huge flexibility by allowing parties to provide multiple
        inputs (either other contracts or P2PKH).
        Then, we check scriptOutput to be correct.
     -}
    validSignatures = let
        requiredSignatures = getSignatures inputs
        in checkSignatures pendingTx requiredSignatures

    PendingTxIn _ _ scriptInValue = pendingTxIn

    -- total balance of all accounts in State
    -- accounts must be positive, and we checked it above
    inputBalance = totalBalance (accounts marloweState)

    -- ensure that a contract TxOut has what it suppose to have
    balancesOk = inputBalance == scriptInValue

    preconditionsOk = checkCreator
        && positiveBalances
        && validSignatures
        && balancesOk

    slotInterval = (minSlot, maxSlot)
    txInput = TransactionInput { txInterval = slotInterval, txInputs = inputs }
    expectedTxOutputs = computeTransaction txInput marloweState marloweContract

    outputOk = validateTxOutputs pendingTx creator expectedTxOutputs

    in preconditionsOk && outputOk


-- Typeclass instances

instance Eq AccountId where
    {-# INLINABLE (==) #-}
    (AccountId n1 p1) == (AccountId n2 p2) = n1 == n2 && p1 == p2


instance Eq ChoiceId where
    {-# INLINABLE (==) #-}
    (ChoiceId n1 p1) == (ChoiceId n2 p2) = n1 == n2 && p1 == p2

instance Eq Token where
    {-# INLINABLE (==) #-}
    (Token n1 p1) == (Token n2 p2) = n1 == n2 && p1 == p2

instance Eq ValueId where
    {-# INLINABLE (==) #-}
    (ValueId n1) == (ValueId n2) = n1 == n2


instance Read ValueId where
    readsPrec p x = [(ValueId v, s) | (v, s) <- readsPrec p x]


instance Pretty ValueId where
    prettyFragment (ValueId n) = prettyFragment n

instance Eq Payee where
    {-# INLINABLE (==) #-}
    Account acc1 == Account acc2 = acc1 == acc2
    Party p1 == Party p2 = p1 == p2
    _ == _ = False


instance Eq Payment where
    {-# INLINABLE (==) #-}
    Payment p1 m1 == Payment p2 m2 = p1 == p2 && m1 == m2


instance Eq ReduceWarning where
    {-# INLINABLE (==) #-}
    ReduceNoWarning == ReduceNoWarning = True
    (ReduceNonPositivePay acc1 p1 tn1 a1) == (ReduceNonPositivePay acc2 p2 tn2 a2) =
        acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2
    (ReducePartialPay acc1 p1 tn1 a1 e1) == (ReducePartialPay acc2 p2 tn2 a2 e2) =
        acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2 && e1 == e2
    (ReduceShadowing v1 old1 new1) == (ReduceShadowing v2 old2 new2) =
        v1 == v2 && old1 == old2 && new1 == new2
    _ == _ = False


instance Eq ReduceEffect where
    {-# INLINABLE (==) #-}
    ReduceNoPayment == ReduceNoPayment = True
    ReduceWithPayment p1 == ReduceWithPayment p2 = p1 == p2
    _ == _ = False


instance Eq Value where
    {-# INLINABLE (==) #-}
    AvailableMoney acc1 tok1 == AvailableMoney acc2 tok2 =
        acc1 == acc2 && tok1 == tok2
    Constant i1 == Constant i2 = i1 == i2
    NegValue val1 == NegValue val2 = val1 == val2
    AddValue val1 val2 == AddValue val3 val4 = val1 == val3 && val2 == val4
    SubValue val1 val2 == SubValue val3 val4 = val1 == val3 && val2 == val4
    ChoiceValue cid1 val1 == ChoiceValue cid2 val2 = cid1 == cid2 && val1 == val2
    SlotIntervalStart == SlotIntervalStart = True
    SlotIntervalEnd   == SlotIntervalEnd   = True
    UseValue val1 == UseValue val2 = val1 == val2
    _ == _ = False


instance Eq Observation where
    {-# INLINABLE (==) #-}
    AndObs o1l o2l == AndObs o1r o2r = o1l == o1r && o2l == o2r
    OrObs  o1l o2l == OrObs  o1r o2r = o1l == o1r && o2l == o2r
    NotObs ol == NotObs or = ol == or
    ChoseSomething cid1 == ChoseSomething cid2 = cid1 == cid2
    ValueGE v1l v2l == ValueGE v1r v2r = v1l == v1r && v2l == v2r
    ValueGT v1l v2l == ValueGT v1r v2r = v1l == v1r && v2l == v2r
    ValueLT v1l v2l == ValueLT v1r v2r = v1l == v1r && v2l == v2r
    ValueLE v1l v2l == ValueLE v1r v2r = v1l == v1r && v2l == v2r
    ValueEQ v1l v2l == ValueEQ v1r v2r = v1l == v1r && v2l == v2r
    TrueObs  == TrueObs  = True
    FalseObs == FalseObs = True
    _ == _ = False


instance Eq Action where
    {-# INLINABLE (==) #-}
    Deposit acc1 party1 tok1 val1 == Deposit acc2 party2 tok2 val2 =
        acc1 == acc2 && party1 == party2 && tok1 == tok2 && val1 == val2
    Choice cid1 bounds1 == Choice cid2 bounds2 =
        cid1 == cid2 && let
            bounds = zip bounds1 bounds2
            checkBound (Bound low1 high1, Bound low2 high2) = low1 == low2 && high1 == high2
            in all checkBound bounds
    Notify obs1 == Notify obs2 = obs1 == obs2
    _ == _ = False


instance Eq Contract where
    {-# INLINABLE (==) #-}
    Close == Close = True
    Pay acc1 payee1 tok1 value1 cont1 == Pay acc2 payee2 tok2 value2 cont2 =
        acc1 == acc2 && payee1 == payee2 && tok1 == tok2 && value1 == value2 && cont1 == cont2
    If obs1 cont1 cont2 == If obs2 cont3 cont4 =
        obs1 == obs2 && cont1 == cont3 && cont2 == cont4
    When cases1 timeout1 cont1 == When cases2 timeout2 cont2 =
        timeout1 == timeout2 && cont1 == cont2
        && let cases = zip cases1 cases2
               checkCase (Case action1 cont1, Case action2 cont2) =
                    action1 == action2 && cont1 == cont2
           in all checkCase cases
    Let valId1 val1 cont1 == Let valId2 val2 cont2 =
        valId1 == valId2 && val1 == val2 && cont1 == cont2
    _ == _ = False


instance Eq State where
    {-# INLINABLE (==) #-}
    l == r = minSlot l == minSlot r
        && accounts l == accounts r
        && choices l == choices r
        && boundValues l == boundValues r


-- Lifting data types to Plutus Core
makeLift ''AccountId
makeIsData ''AccountId
makeLift ''ChoiceId
makeIsData ''ChoiceId
makeLift ''Token
makeIsData ''Token
makeLift ''ValueId
makeIsData ''ValueId
makeLift ''Value
makeIsData ''Value
makeLift ''Observation
makeIsData ''Observation
makeLift ''Bound
makeIsData ''Bound
makeLift ''Action
makeIsData ''Action
makeLift ''Case
makeIsData ''Case
makeLift ''Payee
makeIsData ''Payee
makeLift ''Contract
makeIsData ''Contract
makeLift ''State
makeIsData ''State
makeLift ''Environment
makeLift ''Input
makeIsData ''Input
makeLift ''IntervalError
makeLift ''IntervalResult
makeLift ''Payment
makeLift ''ReduceEffect
makeLift ''ReduceWarning
makeLift ''ReduceStepResult
makeLift ''ReduceResult
makeLift ''ApplyWarning
makeLift ''ApplyResult
makeLift ''ApplyAllResult
makeLift ''TransactionWarning
makeLift ''TransactionError
makeLift ''TransactionOutput
makeLift ''MarloweData
makeIsData ''MarloweData
