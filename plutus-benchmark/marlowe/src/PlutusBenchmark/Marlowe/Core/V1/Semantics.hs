-- editorconfig-checker-disable-file


-----------------------------------------------------------------------------
--
-- Module      :  $Headers
-- License     :  Apache 2.0
--
-- Stability   :  Experimental
-- Portability :  Portable
--
-- | = Marlowe: financial contracts domain specific language for blockchain
--
--   Here we present a reference implementation of Marlowe, domain-specific language targeted at
--   the execution of financial contracts in the style of Peyton Jones et al
--   on Cardano.
--
--   This is the Haskell implementation of Marlowe semantics for Cardano.
--
--   == Semantics
--
--   Semantics is based on <https://github.com/input-output-hk/marlowe/blob/stable/src/Semantics.hs>
--
--   Marlowe Contract execution is a chain of transactions,
--   where remaining contract and its state is passed through /Datum/,
--   and actions (i.e. /Choices/) are passed as
--   /Redeemer Script/
--
--   /Validation Script/ is always the same Marlowe interpreter implementation, available below.
--
-----------------------------------------------------------------------------


{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -O0 #-}
-- the biggest hammer :(
-- truly mysterious issues here
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}
-- O0 turns these off
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module PlutusBenchmark.Marlowe.Core.V1.Semantics
  ( -- * Semantics
    MarloweData(MarloweData, marloweParams, marloweState, marloweContract)
  , MarloweParams(..)
  , Payment(..)
  , TransactionInput(..)
  , TransactionOutput(..)
  , computeTransaction
  , playTrace
    -- * Supporting Functions
  , addMoneyToAccount
  , applyAction
  , applyAllInputs
  , applyCases
  , applyInput
  , convertReduceWarnings
  , evalObservation
  , evalValue
  , fixInterval
  , getContinuation
  , giveMoney
  , moneyInAccount
  , playTraceAux
  , reduceContractStep
  , reduceContractUntilQuiescent
  , refundOne
  , updateMoneyInAccount
    -- * Supporting Types
  , ApplyAction(..)
  , ApplyAllResult(..)
  , ApplyResult(..)
  , ApplyWarning(..)
  , ReduceEffect(..)
  , ReduceResult(..)
  , ReduceStepResult(..)
  , ReduceWarning(..)
  , TransactionError(..)
  , TransactionWarning(..)
    -- * Utility Functions
  , allBalancesArePositive
  , contractLifespanUpperBound
  , isClose
  , notClose
  , paymentMoney
  , totalBalance
  ) where


import Data.Data (Data)
import GHC.Generics (Generic)
import PlutusBenchmark.Marlowe.Core.V1.Semantics.Types
import PlutusLedgerApi.V2 (CurrencySymbol, POSIXTime (..))
import PlutusTx (FromData, ToData, UnsafeFromData)
import PlutusTx.AsData (asData)
import PlutusTx.IsData (makeIsDataIndexed)
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude (AdditiveGroup ((-)), AdditiveSemigroup ((+)), Bool (..), Eq (..), Integer,
                         Maybe (..), MultiplicativeSemigroup ((*)),
                         Ord (max, min, (<), (<=), (>), (>=)), all, foldMap, foldr, fst, negate,
                         not, otherwise, reverse, snd, ($), (&&), (++), (||))

import PlutusLedgerApi.V2 qualified as Val
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Builtins qualified as Builtins
import Prelude qualified as Haskell



{-| Payment occurs during 'Pay' contract evaluation, and
    when positive balances are payed out on contract closure.
-}
data Payment = Payment AccountId Payee Token Integer
  deriving stock (Haskell.Eq, Haskell.Show, Data)


-- | Extract the money value from a payment.
paymentMoney :: Payment -> Money
paymentMoney (Payment _ _ (Token cur tok) amt) = Val.singleton cur tok amt


-- | Effect of 'reduceContractStep' computation
data ReduceEffect = ReduceWithPayment Payment
                  | ReduceNoPayment
  deriving stock (Haskell.Show, Data)


-- | Warning during 'reduceContractStep'
data ReduceWarning = ReduceNoWarning
                   | ReduceNonPositivePay AccountId Payee Token Integer
                   | ReducePartialPay AccountId Payee Token Integer Integer
--                                      ^ src    ^ dest       ^ paid ^ expected
                   | ReduceShadowing ValueId Integer Integer
--                                     oldVal ^  newVal ^
                   | ReduceAssertionFailed
  deriving stock (Haskell.Show, Data)


-- | Result of 'reduceContractStep'
data ReduceStepResult = Reduced ReduceWarning ReduceEffect State Contract
                      | NotReduced
                      | AmbiguousTimeIntervalReductionError
  deriving stock (Haskell.Show, Data)


-- | Result of 'reduceContractUntilQuiescent'
data ReduceResult = ContractQuiescent Bool [ReduceWarning] [Payment] State Contract
                  | RRAmbiguousTimeIntervalError
  deriving stock (Haskell.Show, Data)


-- | Warning of 'applyCases'
data ApplyWarning = ApplyNoWarning
                  | ApplyNonPositiveDeposit Party AccountId Token Integer
  deriving stock (Haskell.Show, Data)


-- | Result of 'applyCases'
data ApplyResult = Applied ApplyWarning State Contract
                 | ApplyNoMatchError
                 | ApplyHashMismatch
  deriving stock (Haskell.Show, Data)


-- | Result of 'applyAllInputs'
data ApplyAllResult = ApplyAllSuccess Bool [TransactionWarning] [Payment] State Contract
                    | ApplyAllNoMatchError
                    | ApplyAllAmbiguousTimeIntervalError
                    | ApplyAllHashMismatch
  deriving stock (Haskell.Show, Data)


-- | Warnings during transaction computation
data TransactionWarning = TransactionNonPositiveDeposit Party AccountId Token Integer
                        | TransactionNonPositivePay AccountId Payee Token Integer
                        | TransactionPartialPay AccountId Payee Token Integer Integer
--                                                 ^ src    ^ dest     ^ paid   ^ expected
                        | TransactionShadowing ValueId Integer Integer
--                                                 oldVal ^  newVal ^
                        | TransactionAssertionFailed
  deriving stock (Haskell.Show, Generic, Haskell.Eq, Data)


-- | Transaction error
data TransactionError = TEAmbiguousTimeIntervalError
                      | TEApplyNoMatchError
                      | TEIntervalError IntervalError
                      | TEUselessTransaction
                      | TEHashMismatch
  deriving stock (Haskell.Show, Generic, Haskell.Eq, Data)


-- | Marlowe transaction input.
data TransactionInput = TransactionInput
    { txInterval :: TimeInterval
    , txInputs   :: [Input] }
  deriving stock (Haskell.Show, Haskell.Eq, Data)


-- | Marlowe transaction output.
data TransactionOutput =
    TransactionOutput
        { txOutWarnings :: [TransactionWarning]
        , txOutPayments :: [Payment]
        , txOutState    :: State
        , txOutContract :: Contract }
    | Error TransactionError
  deriving stock (Haskell.Show, Data)


-- | Parameters constant during the course of a contract.
newtype MarloweParams = MarloweParams { rolesCurrency :: CurrencySymbol }
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord, Data)

makeIsDataIndexed ''MarloweParams [('MarloweParams, 0)]

asData
  [d|
  -- | This data type is a content of a contract's /Datum/
  data MarloweData = MarloweData {
          marloweParams   :: MarloweParams,
          marloweState    :: State,
          marloweContract :: Contract
      }
      deriving stock (Generic, Data)
      deriving newtype (ToData, FromData, UnsafeFromData, Haskell.Show, Haskell.Eq)
  |]

{-# INLINABLE MarloweData #-}

-- | Checks 'interval' and trims it if necessary.
fixInterval :: TimeInterval -> State -> IntervalResult
fixInterval interval state =
    case interval of
        (low, high)
          | high < low -> IntervalError (InvalidInterval interval)
          | otherwise -> let
            curMinTime = minTime state
            -- newLow is both new "low" and new "minTime" (the lower bound for slotNum)
            newLow = max low curMinTime
            -- We know high is greater or equal than newLow (prove)
            curInterval = (newLow, high)
            env = Environment { timeInterval = curInterval }
            newState = state { minTime = newLow }
            in if high < curMinTime then IntervalError (IntervalInPastError curMinTime interval)
            else IntervalTrimmed env newState


-- | Evaluates @Value@ given current @State@ and @Environment@.
evalValue :: Environment -> State -> Value Observation -> Integer
evalValue env state value = let
    eval = evalValue env state
    in case value of
        AvailableMoney accId token -> moneyInAccount accId token (accounts state)
        Constant integer     -> integer
        NegValue val         -> negate (eval val)
        AddValue lhs rhs     -> eval lhs + eval rhs
        SubValue lhs rhs     -> eval lhs - eval rhs
        MulValue lhs rhs     -> eval lhs * eval rhs
        DivValue lhs rhs     -> let n = eval lhs
                                    d = eval rhs
                                in if d == 0
                                   then 0
                                   else n `Builtins.quotientInteger` d
        ChoiceValue choiceId ->
            -- SCP-5126: Given the precondition that `choices` contains no
            -- duplicate entries, this lookup behaves identically to
            -- Marlowe's Isabelle semantics given the precondition that
            -- the initial state's `choices` in Isabelle was sorted and
            -- did not contain duplicate entries.
            case Map.lookup choiceId (choices state) of
                Just x  -> x
                Nothing -> 0
        TimeIntervalStart    -> getPOSIXTime (fst (timeInterval env))
        TimeIntervalEnd      -> getPOSIXTime (snd (timeInterval env))
        UseValue valId       ->
            -- SCP-5126: Given the precondition that `boundValues` contains
            -- no duplicate entries, this lookup behaves identically to
            -- Marlowe's Isabelle semantics given the precondition that
            -- the initial state's `boundValues` in Isabelle was sorted
            -- and did not contain duplicate entries.
            case Map.lookup valId (boundValues state) of
                Just x  -> x
                Nothing -> 0
        Cond cond thn els    -> if evalObservation env state cond then eval thn else eval els


-- | Evaluate 'Observation' to 'Bool'.
evalObservation :: Environment -> State -> Observation -> Bool
evalObservation env state obs = let
    evalObs = evalObservation env state
    evalVal = evalValue env state
    in case obs of
        AndObs lhs rhs          -> evalObs lhs && evalObs rhs
        OrObs lhs rhs           -> evalObs lhs || evalObs rhs
        NotObs subObs           -> not (evalObs subObs)
                                   -- SCP-5126: Given the precondition that `choices` contains no
                                   -- duplicate entries, this membership test behaves identically
                                   -- to Marlowe's Isabelle semantics given the precondition that
                                   -- the initial state's `choices` in Isabelle was sorted and did
                                   -- not contain duplicate entries.
        ChoseSomething choiceId -> choiceId `Map.member` choices state
        ValueGE lhs rhs         -> evalVal lhs >= evalVal rhs
        ValueGT lhs rhs         -> evalVal lhs > evalVal rhs
        ValueLT lhs rhs         -> evalVal lhs < evalVal rhs
        ValueLE lhs rhs         -> evalVal lhs <= evalVal rhs
        ValueEQ lhs rhs         -> evalVal lhs == evalVal rhs
        TrueObs                 -> True
        FalseObs                -> False


-- | Pick the first account with money in it.
refundOne :: Accounts -> Maybe ((Party, Token, Integer), Accounts)
refundOne accounts = case Map.toList accounts of
    [] -> Nothing
    -- SCP-5126: The return value of this function differs from
    -- Isabelle semantics in that it returns the least-recently
    -- added account-token combination rather than the first
    -- lexicographically ordered one. Also, the sequence
    -- `Map.fromList . tail . Map.toList` preserves the
    -- invariants of order and non-duplication.
    ((accId, token), balance) : rest ->
        if balance > 0
        then Just ((accId, token, balance), Map.fromList rest)
        else refundOne (Map.fromList rest)


-- | Obtains the amount of money available an account.
moneyInAccount :: AccountId -> Token -> Accounts -> Integer
moneyInAccount accId token accounts =
    -- SCP-5126: Given the precondition that `accounts` contains
    -- no duplicate entries, this lookup behaves identically to
    -- Marlowe's Isabelle semantics given the precondition that
    -- the initial state's `accounts` in Isabelle was sorted and
    -- did not contain duplicate entries.
    case Map.lookup (accId, token) accounts of
      Just x  -> x
      Nothing -> 0


-- | Sets the amount of money available in an account.
updateMoneyInAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
updateMoneyInAccount accId token amount =
    -- SCP-5126: Given the precondition that `accounts` contains
    -- no duplicate entries, this deletion or insertion behaves
    -- identically (aside from internal ordering) to Marlowe's
    -- Isabelle semantics given the precondition that the initial
    -- state's `accounts` in Isabelle was sorted and did not
    -- contain duplicate entries.
    if amount <= 0 then Map.delete (accId, token) else Map.insert (accId, token) amount


-- | Add the given amount of money to an account (only if it is positive).
--   Return the updated Map.
addMoneyToAccount :: AccountId -> Token -> Integer -> Accounts -> Accounts
addMoneyToAccount accId token amount accounts = let
    balance = moneyInAccount accId token accounts
    newBalance = balance + amount
    in if amount <= 0 then accounts
    else updateMoneyInAccount accId token newBalance accounts


-- | Gives the given amount of money to the given payee.
--   Returns the appropriate effect and updated accounts.
giveMoney :: AccountId -> Payee -> Token -> Integer -> Accounts -> (ReduceEffect, Accounts)
giveMoney accountId payee token amount accounts = let
    newAccounts = case payee of
        Party _       -> accounts
        Account accId -> addMoneyToAccount accId token amount accounts
    in (ReduceWithPayment (Payment accountId payee token amount), newAccounts)


-- | Carry a step of the contract with no inputs.
reduceContractStep :: Environment -> State -> Contract -> ReduceStepResult
reduceContractStep env state contract = case contract of

    -- SCP-5126: Although `refundOne` refunds accounts-token combinations
    -- in least-recently-added order and Isabelle semantics requires that
    -- they be refunded in lexicographic order, `reduceContractUntilQuiescent`
    -- ensures that the `Close` pattern will be executed until `accounts`
    -- is empty. Thus, the net difference between the behavior here and the
    -- Isabelle semantics is that the `ContractQuiescent` resulting from
    -- `reduceContractUntilQuiescent` will contain payments in a different
    -- order.
    Close -> case refundOne (accounts state) of
        Just ((party, token, amount), newAccounts) -> let
            newState = state { accounts = newAccounts }
            in Reduced ReduceNoWarning (ReduceWithPayment (Payment party (Party party) token amount)) newState Close
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
                (payment, finalAccs) = giveMoney accId payee tok paidAmount newAccs
                newState = state { accounts = finalAccs }
                in Reduced warning payment newState cont

    If obs cont1 cont2 -> let
        cont = if evalObservation env state obs then cont1 else cont2
        in Reduced ReduceNoWarning ReduceNoPayment state cont

    When _ timeout cont -> let
        (startTime, endTime) = timeInterval env
        -- if timeout in future – do not reduce
        in if endTime < timeout then NotReduced
        -- if timeout in the past – reduce to timeout continuation
        else if timeout <= startTime then Reduced ReduceNoWarning ReduceNoPayment state cont
        -- if timeout in the time range – issue an ambiguity error
        else AmbiguousTimeIntervalReductionError

    Let valId val cont -> let
        evaluatedValue = evalValue env state val
        boundVals = boundValues state
        -- SCP-5126: Given the precondition that `boundValues` contains
        -- no duplicate entries, this insertion behaves identically
        -- (aside from internal ordering) to Marlowe's Isabelle semantics
        -- given the precondition that the initial state's `boundValues`
        -- in Isabelle was sorted and did not contain duplicate entries.
        newState = state { boundValues = Map.insert valId evaluatedValue boundVals }
        -- SCP-5126: Given the precondition that `boundValues` contains
        -- no duplicate entries, this lookup behaves identically to
        -- Marlowe's Isabelle semantics given the precondition that the
        -- initial state's `boundValues` in Isabelle was sorted and did
        -- not contain duplicate entries.
        warn = case Map.lookup valId boundVals of
              Just oldVal -> ReduceShadowing valId oldVal evaluatedValue
              Nothing     -> ReduceNoWarning
        in Reduced warn ReduceNoPayment newState cont

    Assert obs cont -> let
        warning = if evalObservation env state obs
                  then ReduceNoWarning
                  else ReduceAssertionFailed
        in Reduced warning ReduceNoPayment state cont


-- | Reduce a contract until it cannot be reduced more.
reduceContractUntilQuiescent :: Environment -> State -> Contract -> ReduceResult
reduceContractUntilQuiescent env state contract = let
    reductionLoop
      :: Bool -> Environment -> State -> Contract -> [ReduceWarning] -> [Payment] -> ReduceResult
    reductionLoop reduced env state contract warnings payments =
        case reduceContractStep env state contract of
            Reduced warning effect newState cont -> let
                newWarnings = case warning of
                                ReduceNoWarning -> warnings
                                _               -> warning : warnings
                newPayments  = case effect of
                    ReduceWithPayment payment -> payment : payments
                    ReduceNoPayment           -> payments
                in reductionLoop True env newState cont newWarnings newPayments
            AmbiguousTimeIntervalReductionError -> RRAmbiguousTimeIntervalError
            -- this is the last invocation of reductionLoop, so we can reverse lists
            NotReduced -> ContractQuiescent reduced (reverse warnings) (reverse payments) state contract

    in reductionLoop False env state contract [] []


-- | Result of applying an action to a contract.
data ApplyAction = AppliedAction ApplyWarning State
                 | NotAppliedAction
  deriving stock (Haskell.Show, Data)


-- | Try to apply a single input content to a single action.
applyAction :: Environment -> State -> InputContent -> Action -> ApplyAction
applyAction env state (IDeposit accId1 party1 tok1 amount) (Deposit accId2 party2 tok2 val) =
    if accId1 == accId2 && party1 == party2 && tok1 == tok2 && amount == evalValue env state val
    then let warning = if amount > 0 then ApplyNoWarning
                       else ApplyNonPositiveDeposit party2 accId2 tok2 amount
             newAccounts = addMoneyToAccount accId1 tok1 amount (accounts state)
             newState = state { accounts = newAccounts }
         in AppliedAction warning newState
    else NotAppliedAction
applyAction _ state (IChoice choId1 choice) (Choice choId2 bounds) =
    if choId1 == choId2 && inBounds choice bounds
    -- SCP-5126: Given the precondition that `choices` contains no
    -- duplicate entries, this insertion behaves identically (aside
    -- from internal ordering) to Marlowe's Isabelle semantics
    -- given the precondition that the initial state's `choices`
    -- in Isabelle was sorted and did not contain duplicate entries.
    then let newState = state { choices = Map.insert choId1 choice (choices state) }
         in AppliedAction ApplyNoWarning newState
    else NotAppliedAction
applyAction env state INotify (Notify obs)
    | evalObservation env state obs = AppliedAction ApplyNoWarning state
applyAction _ _ _ _ = NotAppliedAction


-- | Try to get a continuation from a pair of Input and Case.
getContinuation :: Input -> Case Contract -> Maybe Contract
getContinuation (NormalInput _) (Case _ continuation) = Just continuation
getContinuation (MerkleizedInput _ inputContinuationHash continuation) (MerkleizedCase _ continuationHash) =
    if inputContinuationHash == continuationHash
    then Just continuation
    else Nothing
getContinuation _ _ = Nothing

-- | Try to apply an input to a list of cases, accepting the first match.
applyCases :: Environment -> State -> Input -> [Case Contract] -> ApplyResult
applyCases env state input (headCase : tailCases) =
    let inputContent = getInputContent input :: InputContent
        action = getAction headCase :: Action
        maybeContinuation = getContinuation input headCase :: Maybe Contract
    in case applyAction env state inputContent action of
         AppliedAction warning newState ->
           -- Note that this differs from Isabelle semantics because
           -- the Cardano semantics includes merkleization.
           case maybeContinuation of
             Just continuation -> Applied warning newState continuation
             Nothing           -> ApplyHashMismatch
         NotAppliedAction -> applyCases env state input tailCases
applyCases _ _ _ [] = ApplyNoMatchError


-- | Apply a single @Input@ to a current contract.
applyInput :: Environment -> State -> Input -> Contract -> ApplyResult
applyInput env state input (When cases _ _) = applyCases env state input cases
applyInput _ _ _ _                          = ApplyNoMatchError


-- | Propagate 'ReduceWarning' to 'TransactionWarning'.
convertReduceWarnings :: [ReduceWarning] -> [TransactionWarning]
convertReduceWarnings = foldr (\warn acc -> case warn of  -- Note that `foldr` is used here for efficiency, differing from Isabelle.
    ReduceNoWarning -> acc
    ReduceNonPositivePay accId payee tok amount ->
        TransactionNonPositivePay accId payee tok amount : acc
    ReducePartialPay accId payee tok paid expected ->
        TransactionPartialPay accId payee tok paid expected : acc
    ReduceShadowing valId oldVal newVal ->
        TransactionShadowing valId oldVal newVal : acc
    ReduceAssertionFailed ->
        TransactionAssertionFailed : acc
    ) []


-- | Apply a list of Inputs to the contract.
applyAllInputs :: Environment -> State -> Contract -> [Input] -> ApplyAllResult
applyAllInputs env state contract inputs = let
    applyAllLoop
        :: Bool
        -> Environment
        -> State
        -> Contract
        -> [Input]
        -> [TransactionWarning]
        -> [Payment]
        -> ApplyAllResult
    applyAllLoop contractChanged env state contract inputs warnings payments =
        case reduceContractUntilQuiescent env state contract of
            RRAmbiguousTimeIntervalError -> ApplyAllAmbiguousTimeIntervalError
            ContractQuiescent reduced reduceWarns pays curState cont ->
              let
                warnings' = warnings ++ convertReduceWarnings reduceWarns
                payments' = payments ++ pays
              in case inputs of
                [] -> ApplyAllSuccess
                    (contractChanged || reduced)
                    warnings'
                    payments'
                    curState
                    cont
                (input : rest) -> case applyInput env curState input cont of
                    Applied applyWarn newState cont' ->
                        applyAllLoop
                            True
                            env
                            newState
                            cont'
                            rest
                            (warnings' ++ convertApplyWarning applyWarn)
                            payments'
                    ApplyNoMatchError -> ApplyAllNoMatchError
                    ApplyHashMismatch -> ApplyAllHashMismatch
    in applyAllLoop False env state contract inputs [] []
  where
    convertApplyWarning :: ApplyWarning -> [TransactionWarning]
    convertApplyWarning warn =
        case warn of
            ApplyNoWarning -> []
            ApplyNonPositiveDeposit party accId tok amount ->
                [TransactionNonPositiveDeposit party accId tok amount]


-- | Check if a contract is just @Close@.
isClose :: Contract -> Bool
isClose Close = True
isClose _     = False


-- | Check if a contract is not just @Close@.
notClose :: Contract -> Bool
notClose Close = False
notClose _     = True


-- | Try to compute outputs of a transaction given its inputs, a contract, and it's @State@
computeTransaction :: TransactionInput -> State -> Contract -> TransactionOutput
computeTransaction tx state contract = let
    inputs = txInputs tx
    in case fixInterval (txInterval tx) state of
        IntervalTrimmed env fixState -> case applyAllInputs env fixState contract inputs of
            ApplyAllSuccess reduced warnings payments newState cont ->
                   if not reduced && (notClose contract || (Map.null $ accounts state))
                    then Error TEUselessTransaction
                    else TransactionOutput { txOutWarnings = warnings
                                           , txOutPayments = payments
                                           , txOutState = newState
                                           , txOutContract = cont }
            ApplyAllNoMatchError -> Error TEApplyNoMatchError
            ApplyAllAmbiguousTimeIntervalError -> Error TEAmbiguousTimeIntervalError
            ApplyAllHashMismatch -> Error TEHashMismatch
        IntervalError error -> Error (TEIntervalError error)

-- | Run a set of inputs starting from the results of a transaction, reporting the new result.
playTraceAux :: TransactionOutput -> [TransactionInput] -> TransactionOutput
playTraceAux res [] = res
playTraceAux TransactionOutput
                { txOutWarnings = warnings
                , txOutPayments = payments
                , txOutState = state
                , txOutContract = cont } (h:t) =
    let transRes = computeTransaction h state cont
     in case transRes of
          TransactionOutput{..} ->
              playTraceAux TransactionOutput
                              { txOutPayments = payments ++ txOutPayments
                              , txOutWarnings = warnings ++ txOutWarnings
                              , txOutState
                              , txOutContract
                              } t
          Error _ -> transRes
playTraceAux err@(Error _) _ = err


-- | Run a set of inputs starting from a contract and empty state, reporting the result.
playTrace :: POSIXTime -> Contract -> [TransactionInput] -> TransactionOutput
playTrace minTime c = playTraceAux TransactionOutput
                                 { txOutWarnings = []
                                 , txOutPayments = []
                                 , txOutState = emptyState minTime
                                 , txOutContract = c
                                 }


-- | Calculates an upper bound for the maximum lifespan of a contract (assuming is not merkleized)
contractLifespanUpperBound :: Contract -> POSIXTime
contractLifespanUpperBound contract = case contract of
    Close -> 0
    Pay _ _ _ _ cont -> contractLifespanUpperBound cont
    If _ contract1 contract2 ->
        max (contractLifespanUpperBound contract1) (contractLifespanUpperBound contract2)
    When cases timeout subContract -> let
        contractsLifespans = [contractLifespanUpperBound c | Case _ c <- cases]
        in Haskell.maximum (timeout : contractLifespanUpperBound subContract : contractsLifespans)
    Let _ _ cont -> contractLifespanUpperBound cont
    Assert _ cont -> contractLifespanUpperBound cont


-- | Total the balance in all accounts.
totalBalance :: Accounts -> Money
totalBalance accounts = foldMap
    (\((_, Token cur tok), balance) -> Val.singleton cur tok balance)
    (Map.toList accounts)


-- | Check that all accounts have positive balance.
allBalancesArePositive :: State -> Bool
allBalancesArePositive State{..} = all (\(_, balance) -> balance > 0) (Map.toList accounts)


instance Eq Payment where
    {-# INLINABLE (==) #-}
    Payment a1 p1 t1 i1 == Payment a2 p2 t2 i2 = a1 == a2 && p1 == p2 && t1 == t2 && i1 == i2


instance Eq ReduceWarning where
    {-# INLINABLE (==) #-}
    ReduceNoWarning == ReduceNoWarning = True
    ReduceNoWarning == _ = False
    ReduceNonPositivePay acc1 p1 tn1 a1 == ReduceNonPositivePay acc2 p2 tn2 a2 =
        acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2
    ReduceNonPositivePay{} == _ = False
    ReducePartialPay acc1 p1 tn1 a1 e1 == ReducePartialPay acc2 p2 tn2 a2 e2 =
        acc1 == acc2 && p1 == p2 && tn1 == tn2 && a1 == a2 && e1 == e2
    ReducePartialPay{} == _ = False
    ReduceShadowing v1 old1 new1 == ReduceShadowing v2 old2 new2 =
        v1 == v2 && old1 == old2 && new1 == new2
    ReduceShadowing{} == _ = False
    ReduceAssertionFailed == ReduceAssertionFailed = True
    ReduceAssertionFailed == _ = False


instance Eq ReduceEffect where
    {-# INLINABLE (==) #-}
    ReduceNoPayment == ReduceNoPayment           = True
    ReduceNoPayment == _                         = False
    ReduceWithPayment p1 == ReduceWithPayment p2 = p1 == p2
    ReduceWithPayment _ == _                     = False

-- Functions that used in Plutus Core must be inlineable,
-- so their code is available for PlutusTx compiler.
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
{-# INLINABLE applyAction #-}
{-# INLINABLE getContinuation #-}
{-# INLINABLE applyCases #-}
{-# INLINABLE applyInput #-}
{-# INLINABLE convertReduceWarnings #-}
{-# INLINABLE applyAllInputs #-}
{-# INLINABLE isClose #-}
{-# INLINABLE notClose #-}
{-# INLINABLE computeTransaction #-}
{-# INLINABLE contractLifespanUpperBound #-}
{-# INLINABLE totalBalance #-}


-- Lifting data types to Plutus Core
makeLift ''IntervalError
makeLift ''IntervalResult
makeLift ''Payment
makeLift ''ReduceEffect
makeLift ''ReduceWarning
makeLift ''ReduceStepResult
makeLift ''ReduceResult
makeLift ''ApplyWarning
makeLift ''ApplyResult
makeLift ''TransactionWarning
makeLift ''ApplyAllResult
makeLift ''TransactionError
makeLift ''TransactionOutput
makeLift ''MarloweParams
makeLift ''MarloweData
