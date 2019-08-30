First, the language extensions and imports.

[source,haskell]
----
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- Big hammer, but helps
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}

{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Language.Marlowe.Common where

import qualified Prelude                    as Haskell

import           GHC.Generics               (Generic)
import           Language.Marlowe.Pretty    (Pretty, prettyFragment)
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift     (makeLift)
import           Language.PlutusTx.Prelude
import           Ledger                     (PubKey (..), Signature (..), Slot (..))
import           Ledger.Ada                 (Ada)
import qualified Ledger.Ada                 as Ada
import           Ledger.Interval            (Interval (..))
import           Ledger.Scripts             (DataScriptHash (..), RedeemerHash (..))
import           Ledger.Validation
import           LedgerBytes                (LedgerBytes (..))
import           Text.PrettyPrint.Leijen    (text)

{-# ANN module ("HLint: ignore"::String) #-}

-- type synonyms for timeouts, cash, and the public key identifier of a contract participant
type Timeout = Integer
type Cash = Integer

type Person = PubKey

instance Pretty PubKey where
    prettyFragment = text . show
----

Below we give the data types we use as the unique identifiers for cash commits,
payments and choices made by participants. These are not automatically generated,
but the uniqueness condition is checked as part of validation.

[source,haskell]
----


{-
This is the identifier for a commit cash action, which can be used to refer to this
particular committed cash throughout the rest of the contract
-}

newtype IdentCC = IdentCC Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

{-|
This is identifier for a choice made by a participant, which can be used
throughout the rest of the contract to look up
the particular value chosen, and the identifier for the person who made the choice
-}

newtype IdentChoice = IdentChoice Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

-- the identifier for a payment (i.e. funds released from the contract to a participant)

newtype IdentPay = IdentPay Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

type ConcreteChoice = Integer

-- CCStatus gives the status for a commit, specifically
-- the person who made the commit, the amount of cash left in the commit
-- and the time the commit expires and is refunded
type CCStatus = (Person, CCRedeemStatus)

data CCRedeemStatus = NotRedeemed Cash Timeout
               deriving (Haskell.Eq, Haskell.Ord, Show)

instance Eq CCRedeemStatus where
    {-# INLINABLE (==) #-}
    (NotRedeemed c1 t1) == (NotRedeemed c2 t2) = c1 == c2 && t1 == t2

type Choice = ((IdentChoice, Person), ConcreteChoice)

type Commit = (IdentCC, CCStatus)

{-|
Value is a set of contract primitives that represent constants,
functions, and variables that can be evaluated as an amount
of money.

An oracle value is a value provided (and signed by) a `PubKey` that represents
a piece of data sourced from the "real world". For example, the price of a product
at a given point in time.
-}
data Value  = Committed IdentCC
            -- ^ available amount by 'IdentCC'
            | Value Integer
            | AddValue Value Value
            | MulValue Value Value
            | DivValue Value Value Value
            -- ^ dividend, divisor, default value (when divisor evaluates to 0)
            | ValueFromChoice IdentChoice Person Value
            -- ^ interpret a choice identified by 'IdentChoice' and 'Person' as a value if it is provided,
            --   'Value' otherwise
            | ValueFromOracle PubKey Value
            -- ^ Oracle PubKey, default 'Value' when no Oracle Value provided
               deriving stock (Haskell.Eq, Show, Generic)
               deriving anyclass (Pretty)


instance Eq Value where
    {-# INLINABLE (==) #-}
    l == r = case (l, r) of
        (Committed idl, Committed idr) -> idl == idr
        (Value vl, Value vr) -> vl == vr
        (AddValue v1l v2l, AddValue v1r v2r) -> v1l == v1r && v2l == v2r
        (MulValue v1l v2l, MulValue v1r v2r) -> v1l == v1r && v2l == v2r
        (DivValue v1l v2l v3l, DivValue v1r v2r v3r) ->
            v1l == v1r
            && v2l == v2r
            && v3l == v3r
        (ValueFromChoice (IdentChoice idl) pkl vl, ValueFromChoice (IdentChoice idr) pkr vr) ->
            idl == idr
            && pkl == pkr
            && vl == vr
        (ValueFromOracle pkl vl, ValueFromOracle pkr vr) -> pkl == pkr && vl == vr
        _ -> False

----

    Observation is a constructor for predicates on outer world and contract 'State'.
    It represents the subset of predicates
    which can be evaluated within a contract.

[source,haskell]
----
data Observation = BelowTimeout Integer
            -- ^ the current time is less than or equal to the given integer
            | AndObs Observation Observation
            | OrObs Observation Observation
            | NotObs Observation
            | PersonChoseThis IdentChoice Person ConcreteChoice
            | PersonChoseSomething IdentChoice Person
            | ValueGE Value Value
            -- ^ first amount is greater than or equal to the second
            | TrueObs
            | FalseObs
               deriving stock (Haskell.Eq, Show, Generic)
               deriving anyclass (Pretty)

instance Eq Observation where
    {-# INLINABLE (==) #-}
    l == r = case (l, r) of
            (BelowTimeout tl, BelowTimeout tr) -> tl == tr
            (AndObs o1l o2l, AndObs o1r o2r) -> o1l == o1r && o2l == o2r
            (OrObs o1l o2l, OrObs o1r o2r) -> o1l == o1r && o2l == o2r
            (NotObs ol, NotObs or) -> ol == or
            (PersonChoseThis (IdentChoice idl) pkl cl, PersonChoseThis (IdentChoice idr) pkr cr) ->
                idl == idr && pkl == pkr && cl == cr
            (PersonChoseSomething (IdentChoice idl) pkl, PersonChoseSomething (IdentChoice idr) pkr) ->
                idl == idr && pkl == pkr
            (ValueGE v1l v2l, ValueGE v1r v2r) -> v1l == v1r && v2l == v2r
            (TrueObs, TrueObs) -> True
            (FalseObs, FalseObs) -> True
            _ -> False

{-| Marlowe Contract Data Type
-}
data Contract = Null                                                             -- <1>
            | CommitCash IdentCC PubKey Value Timeout Timeout Contract Contract  -- <2>
            | RedeemCC IdentCC Contract                                          -- <3>
            | Pay IdentPay Person Person Value Timeout Contract                  -- <4>
            | Both Contract Contract                                             -- <5>
            | Choice Observation Contract Contract                               -- <6>
            | When Observation Timeout Contract Contract                         -- <7>
               deriving stock (Haskell.Eq, Show, Generic)
               deriving anyclass (Pretty)
----
<1> `Null` is the trivial contract, where no participants can perform any actions
and there is no more program to execute. This contract is always fulfilled!

<2> `CommitCash idC pk v t1 t2 c1 c2` constructor allows a participant to commit cash
to a contract, taking the following arguments

* `idC` - unique identifier of this cash commit
* `pk`  - the (public key) ID of the person who is expected to commit the cash
* `v`   - the amount of cash to be committed
* `t1`  - the block (slot) number after which the commit can no longer be made,
and the contract continues as `c2`
* `t2`  - the block (slot) number after which the cash committed by `pk` to this
contract will be returned to `pk` at this time, and every other commit belonging to
the contract at that time will also be returned to the participant who made it
* `c1`  - the contract as which `CommitCash idC pk v t1 t2 c1 c2` continues
when `p` makes the commit (of value `v` before time `t1`)
* `c2`  - the contract as which `CommitCash idC pk v t1 t2 c1 c2` continues
when `p` does not make the correct cash commit before the timeout

<3> `Redeem idC c` constructor represents the contract which refunds the cash
from commit with identity `idC` and proceeds as contract `c`

<4> `Pay idC pk1 pk2 v t c` constructor represents the contract paying
the cash amount `v` committed by person `pk1` to `pk2`, which must be done
before timeout time `t`, and then continue as contract `c`

<5> `Both c1 c2` constructor represents a contract that requires both
`c1` and `c2` to be fulfilled

<6> `Choice obs c1 c2` constructor represents the contract which is equivalent
to (evaluates to) `c1` when `obs` is true, and `c2` otherwise

<7> `When obs t c1 c2` constructor represents the contract that evaluates to
`c1` as soon as `obs` becomes true, provided it is at or before timeout `t`,
otherwise, it evaluates to `c2`

[source,haskell]
----
instance Eq Contract where
    {-# INLINABLE (==) #-}
    l == r = case (l, r) of
            (Null, Null) -> True
            (CommitCash (IdentCC idl) pkl vl t1l t2l c1l c2l, CommitCash (IdentCC idr) pkr vr t1r t2r c1r c2r) ->
                idl == idr
                && pkl == pkr
                && vl == vr
                && t1l == t1r && t2l == t2r
                && c1l ==c1r && c2l == c2r
            (RedeemCC (IdentCC idl) c1l, RedeemCC (IdentCC idr) c1r) -> idl == idr && c1l == c1r
            (Pay (IdentPay idl) pk1l pk2l vl tl cl, Pay (IdentPay idr) pk1r pk2r vr tr cr) ->
                idl == idr
                && pk1l == pk1r
                && pk2l == pk2r
                && vl == vr
                && tl == tr
                && cl == cr
            (Both c1l c2l, Both c1r c2r) -> c1l == c1r && c2l == c2r
            (Choice ol c1l c2l, Choice or c1r c2r) ->
                ol == or
                && c1l == c1r
                && c2l == c2r
            (When ol tl c1l c2l, When or tr c1r c2r) ->
                ol ==  or
                && tl ==  tr
                && c1l == c1r
                && c2l == c2r
            _ -> False


{-|
    This data structure stores the maximum value among the commit IDs,
    and the maximum value among the pay IDs for a given contract. It is
    used in the validation process.
-}
data ValidatorState = ValidatorState {
        maxCCId  :: Integer,
        maxPayId :: Integer
    }
----

The `State` data structure consists of information about the past actions of
contract participants. Specifically, the cash commits and the choices they
have made. This data is also needed to evaluate a term `c :: Contract`, in
addition to external factors such as the current time. The commits are sorted
by ascending expiration time.

[source,haskell]
----
data State = State {
        stateCommitted :: [Commit],
        stateChoices   :: [Choice]
    } deriving (Haskell.Eq, Haskell.Ord, Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    (State commits1 choices1) == (State commits2 choices2) =
        commits1 == commits2 && choices1 == choices2

{-# INLINABLE emptyState #-}
emptyState :: State
emptyState = State { stateCommitted = [], stateChoices = [] }
----

The `InputCommand` data structure is a set of actions that can be performed
on a contract.
    Contract input command.
    'Commit', 'Payment', and 'Redeem' all require a proof
    that the transaction is issued by a particular party identified with /Public Key/.
    We require 'Signature' of TxHash signed with that /Public Key/.

    E.g. if we have
    @ CommitCash ident pubKey (Value 100) ... @
    then we require
    @ Commit ident signature(pubKey) @
    to validate that transaction.

[source,haskell]
----
data InputCommand = Commit IdentCC Signature
    | Payment IdentPay Signature
    | Redeem IdentCC Signature
    | SpendDeposit Signature
    | CreateContract
makeLift ''InputCommand

{-|
    Marlowe Contract Input.
    May contain oracle values and choices.
-}
data Input = Input InputCommand [OracleValue Integer] [Choice]
----

As we have discussed before, the data script of a contract represents its state.
This state must contain all the information necessary to determine what
funds belonging to the script can be unlocked at this time.
and the state of a Marlowe contract is the combination of what the `Contract`
data structure has been evaluated to be at this time, and the commits
and choices that have been made by participants up to this point.

[source,haskell]
----
data MarloweData = MarloweData {
        marloweState    :: State,
        marloweContract :: Contract
    }

makeLift ''IdentCC
makeLift ''IdentChoice
makeLift ''IdentPay
makeLift ''CCRedeemStatus
makeLift ''Value
makeLift ''Observation
makeLift ''Contract
makeLift ''ValidatorState
makeLift ''MarloweData
makeLift ''Input
makeLift ''State
----

The following function, `validateContract`, is _not_ the validator script for
Marlowe contracts. Rather, it is used to check the current validity of a `Contract`
given its `State`, and does not perform contract evaluation.
This validity check consists of making sure the IDs of the
commit and pay actions are valid (unique and stored in the correct order),
and that there is at least as much money locked
by the script (the `actualMoney'` argument) as the sum of the commits.

[source,haskell]
----
{-# INLINABLE validateContract #-}
{-| Contract validation.

    * Check that 'IdentCC' and 'IdentPay' identifiers are unique.
    We require identifiers to appear only in ascending order starting from 1,
    i.e. @ IdentCC 1 @ followed by @ IdentCC 2 @

    * Check that a contract locks at least the value claimed in its State commits.

    [Note] We do not validate 'Observation' because it can't lead to a wrong state.
    Same for 'Value'.
-}
validateContract :: State -> Contract -> Slot -> Ada -> Bool
validateContract State{stateCommitted} contract (Slot bn) actualMoney' = let

    actualMoney = Ada.getLovelace actualMoney'

    calcCommittedMoney :: [Commit] -> Cash -> Cash
    calcCommittedMoney [] r = r
    calcCommittedMoney ((_, (_, NotRedeemed money timeout)) : cs) acc = if bn `Builtins.greaterThanInteger` timeout
        then calcCommittedMoney cs acc
        else calcCommittedMoney cs (acc `Builtins.addInteger` money)

    checkBoth :: ValidatorState -> Contract -> Contract -> (ValidatorState, Bool)
    checkBoth state c1 c2 = let
        (us, valid) = validateIds state c1
        in if valid then validateIds us c2
        else (state, False)

    validateIds :: ValidatorState -> Contract -> (ValidatorState, Bool)
    validateIds state@(ValidatorState maxCCId maxPayId) contract = case contract of
        Null -> (state, True)
        CommitCash (IdentCC id) _ _ _ _ c1 c2 ->
            if id `Builtins.greaterThanInteger` maxCCId
            then checkBoth (ValidatorState id maxPayId) c1 c2
            else (state, False)
        RedeemCC _ c -> validateIds state c
        Pay (IdentPay id) _ _ _ _ c ->
            if id `Builtins.greaterThanInteger` maxPayId
            then validateIds (ValidatorState maxCCId id) c
            else (state, False)
        Both c1 c2 -> checkBoth state c1 c2
        Choice _ c1 c2 -> checkBoth state c1 c2
        When _ _ c1 c2 -> checkBoth state c1 c2

    enoughMoney = calcCommittedMoney stateCommitted 0 <= actualMoney

    in if enoughMoney then
            let (_, validIds) = validateIds (ValidatorState 0 0) contract
            in validIds
       else False
----

Given a value, this function interprets the `Value` constructors and calculates the result
as an integer. All the other parameters of the function are relevant to interpreting
one or several particular `Value` constructors, as explained in the comments.

[source,haskell]
----
{-# INLINABLE evaluateValue #-}
evaluateValue :: Slot -> [OracleValue Integer] -> State -> Value -> Integer
evaluateValue pendingTxSlot inputOracles state value = let

    -- this returns the commit status of a given commit ID if it exists
    -- i.e. whether the commit has already been spent
    -- the commits are passed via the `State` argument of `evaluateValue`
    findCommit :: IdentCC -> [Commit] -> Maybe CCStatus
    findCommit i@(IdentCC searchId) commits = case commits of
        (IdentCC id, status) : _ | id == searchId -> Just status
        _ : xs                                    -> findCommit i xs
        _                                         -> Nothing

    -- this returns an oracle value signed by the owner of a given `PubKey` in a given `Slot`
    -- the oracle values are passed via the `[OracleValue Integer]` of `evaluateValue`
    fromOracle :: PubKey -> Slot -> [OracleValue Integer] -> Maybe Integer
    fromOracle pubKey h@(Slot blockNumber) oracles = case oracles of
        OracleValue pk (Slot bn) value : _
            | pk == pubKey && bn == blockNumber -> Just value
        _ : rest -> fromOracle pubKey h rest
        _ -> Nothing

    -- this returns the choice with a given choice ID if it exists
    -- the choices are passed via the `State` argument of `evaluateValue`s
    fromChoices :: IdentChoice -> PubKey -> [Choice] -> Maybe ConcreteChoice
    fromChoices identChoice@(IdentChoice id) pubKey choices = case choices of
        ((IdentChoice i, party), value) : _ | id == i && party == pubKey -> Just value
        _ : rest                                                         -> fromChoices identChoice pubKey rest
        _                                                                -> Nothing

    -- the function used to interpret and evaluate the given Value
    -- uses above auxiliary functions
    evalValue :: State -> Value -> Integer
    evalValue state@(State committed choices) value = case value of
        Committed ident -> case findCommit ident committed of
            Just (_, NotRedeemed c _) -> c
            _                         -> 0
        Value v -> v
        AddValue lhs rhs -> evalValue state lhs `Builtins.addInteger` evalValue state rhs
        MulValue lhs rhs -> evalValue state lhs `Builtins.multiplyInteger` evalValue state rhs
        DivValue lhs rhs def -> do
            let divident = evalValue state lhs
            let divisor  = evalValue state rhs
            let defVal   = evalValue state def
            if divisor == 0 then defVal else divident `Builtins.divideInteger` divisor
        ValueFromChoice ident pubKey def -> case fromChoices ident pubKey choices of
            Just v -> v
            _      -> evalValue state def
        ValueFromOracle pubKey def -> case fromOracle pubKey pendingTxSlot inputOracles of
            Just v -> v
            _      -> evalValue state def

        in evalValue state value
----

Given an observation, this function interprets the `Observation` constructors and calculates the result
as a `Bool`. All the other parameters of the function are relevant to interpreting
one or several particular `Observation` constructors, as explained in the comments.
The `evalValue` argument, when passed to this function, will be a partial application
of `evaluateValue`, that will be fully applied inside `interpretObservation`.

[source,haskell]
----

{-# INLINABLE interpretObservation #-}
-- | Interpret 'Observation' as 'Bool'.
interpretObservation :: (State -> Value -> Integer) -> Integer -> State -> Observation -> Bool
interpretObservation evalValue blockNumber state@(State _ choices) obs = let

    -- this returns the choice corresponding to a given choice ID, made by a specific person, if it exists
    -- the choices are passed via the `State` argument of `interpretObservation`
    find :: IdentChoice -> Person -> [Choice] -> Maybe ConcreteChoice
    find choiceId@(IdentChoice cid) person choices = case choices of
        (((IdentChoice id, party), choice) : _)
            | cid == id && party == person -> Just choice
        (_ : cs) -> find choiceId person cs
        _ -> Nothing

    -- this function used to interpret and evaluate a given `Observation`
    go :: Observation -> Bool
    go obs = case obs of
        BelowTimeout n -> blockNumber <= n
        AndObs obs1 obs2 -> go obs1 && go obs2
        OrObs obs1 obs2 -> go obs1 || go obs2
        NotObs obs -> not (go obs)
        PersonChoseThis choiceId person referenceChoice ->
            maybe False ((==) referenceChoice) (find choiceId person choices)
        PersonChoseSomething choiceId person -> isJust (find choiceId person choices)
        ValueGE a b -> evalValue state a >= evalValue state b
        TrueObs -> True
        FalseObs -> False
    in go obs

{-# INLINABLE insertCommit #-}
-- | Add a 'Commit', placing it in order by endTimeout per 'Person'
insertCommit :: Commit -> [Commit] -> [Commit]
insertCommit commit commits = let
    insert :: Commit -> [Commit] -> [Commit]
    insert commit commits = let
        (_, (pubKey, NotRedeemed _ endTimeout)) = commit
        in case commits of
            [] -> [commit]
            (_, (pk, NotRedeemed _ t)) : _
                | pk == pubKey && endTimeout < t -> commit : commits
            c : cs -> c : insert commit cs
    in insert commit commits

{-# INLINABLE discountFromPairList #-}
-- | Discounts the Cash from an initial segment of the list of pairs.
discountFromPairList ::
    PubKey
    -> Slot
    -> Ada
    -> [Commit]
    -> Maybe [Commit]
discountFromPairList from (Slot currentBlockNumber) value' commits = let
    value = Ada.getLovelace value'

    discount :: Integer -> [Commit] -> Maybe [Commit]
    discount value commits = case commits of
        (ident, (party, NotRedeemed available expire)) : rest
            | currentBlockNumber <= expire && from == party ->
            if available > value then let
                change = available `Builtins.subtractInteger` value
                updatedCommit = (ident, (party, NotRedeemed change expire))
                in Just (updatedCommit : rest)
            else discount (value `Builtins.subtractInteger` available) rest
        commit : rest -> case discount value rest of
                            Just acc -> Just (commit : acc)
                            Nothing  -> Nothing
        [] -> if value == 0 then Just [] else Nothing
    in discount value commits

{-# INLINABLE findAndRemove #-}
{-| Look for first 'Commit' satisfying @predicate@ and remove it.
    Returns 'Nothing' if the 'Commit' wasn't found,
    otherwise 'Just' modified @[Commit]@
-}
findAndRemove :: (Commit -> Bool) -> [Commit] -> Maybe [Commit]
findAndRemove predicate commits = let
    -- performs early return when found
    findAndRemove :: Bool -> [Commit] -> Maybe [Commit]
    findAndRemove found [] = if found then Just [] else Nothing
    findAndRemove _ (commit : rest) =
        if predicate commit
        then Just rest
        else case findAndRemove False rest of
                Just acc -> Just (commit : acc)
                Nothing  -> Nothing

    in findAndRemove False commits
----

The `evaluateContract` function below computes the updated `State` (i.e. commits
and choices) and `Contract`
resulting from both executing the input command (the `Input` parameter) and the
passage of time.
The two `Ada` arguments to the function are used to check that the amount of cash
committed or collected from the contract address as indicated in the contract
itself (via a `Commit`, `RedeemCC` or `Pay` constructor) is the same
amount (as calculated by examining the inputs and outputs of the transaction
carrying the script) passed to this function by `scriptInValue'` and `scriptOutValue'`.
This check must be done as part of the generalized accounting property, which
describes the total system money flow resulting from a transaction.
The `txHash` and `contractCreatorPK` arguments are used to check signatures, so that
participant actions are authorized by those participants.

The `Bool` in the output
is `True` if contract evaluation is able to progress. It is also `True` when
the contract is evaluated to null, and there
are no commits left in the contract. When contract evaluation is unable to
progress, `(state, contract, False)` is returned with the input
values unchanged.

An example of when contract evaluation may not progress according to the input
command is when a participant attempts to input the `Redeem` command to collect
funds from the contract, but the contract is not defined by the `RedeemCC`
constructor. In this case, `False` is returned as the validation result.

[source,haskell]
----
{-# INLINABLE evaluateContract #-}
{-|
    Evaluates Marlowe Contract
    Returns contract 'State', remaining 'Contract', and validation result.
-}
evaluateContract ::
    PubKey
    -> TxHash
    -> Input
    -> Slot
    -> Ada
    -> Ada
    -> State
    -> Contract -> (State, Contract, Bool)
evaluateContract
    contractCreatorPK
    txHash
    (Input inputCommand inputOracles _)
    blockHeight
    scriptInValue'
    scriptOutValue'
    state
    contract = let

    scriptInValue  = Ada.getLovelace scriptInValue'
    scriptOutValue = Ada.getLovelace scriptOutValue'

    Slot currentBlockNumber = blockHeight

    nullContract :: Contract -> Bool
    nullContract Null = True
    nullContract _    = False

    evalValue :: State -> Value -> Integer
    evalValue = evaluateValue (Slot currentBlockNumber) inputOracles

    interpretObs :: Integer -> State -> Observation -> Bool
    interpretObs = interpretObservation evalValue

    signedBy :: Signature -> PubKey -> Bool
    signedBy (Signature sig) (PubKey (LedgerBytes pk)) = let
        TxHash msg = txHash
        in verifySignature pk msg sig

    -- the evaluation function
    -- for each of the Contract constructors, only need to cover cases
    -- where evaluation progresses
    -- catch-all case at the end for the rest
    eval :: InputCommand -> State -> Contract -> (State, Contract, Bool)
    eval input state@(State commits choices) contract = case (contract, input) of
        (When obs timeout con con2, _)
            | currentBlockNumber > timeout -> eval input state con2
            | interpretObs currentBlockNumber state obs -> eval input state con

        (Choice obs conT conF, _) -> if interpretObs currentBlockNumber state obs
            then eval input state conT
            else eval input state conF

        (Both con1 con2, _) -> (st2, result, isValid1 || isValid2)
            where
                result  | nullContract res1 = res2
                        | nullContract res2 = res1
                        | True =  Both res1 res2
                -- note that full state is accessible in evaluating con1
                (st1, res1, isValid1) = eval input state con1
                -- state resulting from con1 evaluation passed to evaluate con2
                -- this includes any new choices and commits
                (st2, res2, isValid2) = eval input st1 con2

        -- expired CommitCash
        (CommitCash _ _ _ startTimeout endTimeout _ con2, _)
            | currentBlockNumber > startTimeout || currentBlockNumber > endTimeout -> eval input state con2

        (CommitCash id1 pubKey value _ endTimeout con1 _, Commit id2 signature) | id1 == id2 -> let
            vv = evalValue state value

            isValid = vv > 0
                && scriptOutValue == (scriptInValue `Builtins.addInteger` vv)
                && signature `signedBy` pubKey
            in  if isValid then let
                    cns = (pubKey, NotRedeemed vv endTimeout)
                    updatedState = let State committed choices = state
                        in State (insertCommit (id1, cns) committed) choices
                    in (updatedState, con1, True)
                else (state, contract, False)

        (Pay _ _ _ _ timeout con, _)
            | currentBlockNumber > timeout -> eval input state con

        (Pay (IdentPay contractIdentPay) from to payValue _ con, Payment (IdentPay pid) signature) -> let
            pv = evalValue state payValue

            isValid = pid == contractIdentPay
                && pv > 0
                && scriptOutValue == (scriptInValue `Builtins.subtractInteger` pv)
                && signature `signedBy` to
            in  if isValid then let
                in case discountFromPairList from blockHeight (Ada.lovelaceOf pv) commits of
                    Just updatedCommits -> let
                        updatedState = State updatedCommits choices
                        in (updatedState, con, True)
                    Nothing -> (state, contract, False)
            else (state, contract, False)

        (RedeemCC id1 con, Redeem id2 signature) | id1 == id2 -> let
            predicate :: Commit -> Bool
            predicate (i, (pk, NotRedeemed val _)) =
                i == id1
                && scriptOutValue == (scriptInValue `Builtins.subtractInteger` val)
                && signature `signedBy` pk
            -- validate and remove a Commit
            in case findAndRemove predicate commits of
                Just updatedCommits -> (State updatedCommits choices, con, True)
                Nothing             -> (state, contract, False)

        (_, Redeem identCC signature) -> let
            predicate :: Commit -> Bool
            predicate (i, (pk, NotRedeemed val expire)) =
                    i == identCC
                    && scriptOutValue == (scriptInValue `Builtins.subtractInteger` val)
                    && currentBlockNumber > expire
                    && signature `signedBy` pk
            -- validate and remove a Commit
            in case findAndRemove predicate commits of
                Just updatedCommits -> (State updatedCommits choices, contract, True)
                Nothing             -> (state, contract, False)

        -- case when the contract has finished evaluating (is Null)
        -- all commits must have been spent
        -- and check signature
        (Null, SpendDeposit sig) | null commits
            && sig `signedBy` contractCreatorPK -> (state, Null, True)

        -- catch-all for all cases where contract evaluation can't progress
        _ -> (state, Null, False)
    in eval inputCommand state contract

{-# INLINABLE mergeChoices #-}
{-| Merge lists of 'Choice's.
    Return a partialy ordered list of unique choices.
-}
mergeChoices :: [Choice] -> [Choice] -> [Choice]
mergeChoices input choices = let
    insert :: Choice -> [Choice] -> [Choice]
    insert choice choices = let
        in case choices of
            [] -> [choice]
            current@((IdentChoice id, pk), _) : rest -> let
                ((IdentChoice insId, insPK), _) = choice
                in   if insId < id then choice : choices
                else if insId == id then
                        if insPK == pk
                        then choices
                        else current : insert choice rest
                else {- insId > id -} current : insert choice rest

    merge [] choices       = choices
    merge (i:rest) choices = merge rest (insert i choices)
    in merge input choices
----

Now for the final piece of the puzzle: building the validator script.
The function below is not a map to type `ValidatorScript`, but it will be used
in the `Client` module to define the validator script. The first argument
will be passed the `PubKey` of the transaction author, the second argument
is the data script (i.e. the current state and contract), and third is
the redeemer (i.e. the input and the expected result of the evaluation of the
current contract according to this input).

The validation procedure consists of validating both the state and contract
in the data script using the `validateContract` check described above, and
the evaluating it with `evaluateContract`. This function must return `True` as the
validation result, along with state and contract values which are the same
as those passed as the data script parameter (first argument) to `validatorScript`.


[source,haskell]
----
{-# INLINABLE validatorScript #-}
{-|
    Marlowe main Validator Script
-}
validatorScript :: PubKey -> (Input, MarloweData) -> (Input, MarloweData) -> PendingTx -> ()
validatorScript
        creator
        (_ :: Input, MarloweData{..} :: MarloweData)
        (input@(Input inputCommand _ inputChoices :: Input), MarloweData expectedState expectedContract)
        (PendingTx{ pendingTxOutputs, pendingTxValidRange, pendingTxIn, pendingTxHash } :: PendingTx) = let

        {-  Embed contract creator public key. This makes validator script unique,
            which makes a particular contract to have a unique script address.
            That makes it easier to watch for contract actions inside a wallet. -}
        contractCreatorPK = creator

        {-  We require Marlowe Tx to have a lower bound in 'SlotRange'.
            We use it as a current slot, basically. -}
        minSlot = case pendingTxValidRange of
            Interval (Just slot) _ -> slot
            _                      -> traceH "Tx valid slot must have lower bound" Builtins.error ()

        -- TxIn we're validating is obviously a Script TxIn.
        (inputValidatorHash, redeemerHash, scriptInValue) = case pendingTxIn of
            PendingTxIn _ (Just (vHash, RedeemerHash rHash)) value -> (vHash, rHash, value)
            _                                                      -> Builtins.error ()

        scriptInAdaValue = Ada.fromValue scriptInValue

        -- Expected amount of money in TxOut Marlowe Contract
        scriptOutValue = case inputCommand of
            SpendDeposit _ -> zero
            _ -> let (PendingTxOut change
                        (Just (outputValidatorHash, DataScriptHash dataScriptHash)) DataTxOut : _) = pendingTxOutputs
                {-  Check that TxOut is a valid continuation.
                    For that we need to ensure dataScriptHash == redeemerHash
                    and that TxOut has the same validator -}
                 in if dataScriptHash == redeemerHash
                        && inputValidatorHash == outputValidatorHash
                    then Ada.fromValue change else Builtins.error ()

        eval :: Input -> Slot -> Ada -> Ada -> State -> Contract -> (State, Contract, Bool)
        eval = evaluateContract contractCreatorPK pendingTxHash

        contractIsValid = validateContract marloweState marloweContract minSlot scriptInAdaValue

        State currentCommits currentChoices = marloweState

        in if contractIsValid then let
            -- record Choices from Input into State
            mergedChoices = mergeChoices inputChoices currentChoices

            stateWithChoices = State currentCommits mergedChoices

            (newState::State, newCont::Contract, validated) =
                eval input
                    minSlot
                    scriptInAdaValue
                    scriptOutValue
                    stateWithChoices
                    marloweContract

            allowTransaction = validated
                && newCont == expectedContract
                && newState == expectedState

            in if allowTransaction then () else Builtins.error ()
        {-  if the contract is invalid and there are no commit,
            allow to spend contract's money. It's likely to be created by mistake -}
        else if null currentCommits then () else Builtins.error ()
----

[NOTE]
====
.Invalid Initial Data Scripts Are Possible

The `contractIsValid` boolean value is computed on-chain as part of script validation.
When the validator script defined using the above code is applied to the appropriate
arguments (data script, redeemer, transaction and ledger data), this value is true if
the _current_ data script at the UTxO entry the transaction
is attempting to spend is a valid contract and state. The validity of the
evaluated state and contract (i.e. the new data script values which will lock the
funds associated with this contract once the carrying transaction is validated)
is computed by `evaluateContract`.

If this function does not return true,
the transaction is not validated. This means that only valid new data scripts
can end up on the ledger as a result of evaluating existing Marlowe contracts.
However, when paying into a contract initially, _any_ valid Plutus data script can be
submitted in the transaction, even one that is not valid Marlowe.
It does not directly benefit anyone to pay into a contract
where the funds remain locked forever due to an invalid data script. It is
possible, however, that one can potentially be disruptive to the operation
of the blockchain in some way by making unspendable UTxO entries.

This issue of invalid data scripts is not unique to Marlowe contracts. In
general, it is a good idea to define contracts to perform initial data script
validation off-chain, but it is not straightforward to enforce this.

====
