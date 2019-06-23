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

{-| = Marlowe: financial contracts on Cardano Computation Layer

Here we present a reference implementation of Marlowe, domain-specific language targeted at
the execution of financial contracts in the style of Peyton Jones et al
on Cardano Computation Layer.

The implementation is based on semantics described in paper
<https://iohk.io/research/papers/#2WHKDRA8 'Marlowe: financial contracts on blockchain'>
by Simon Thompson and Pablo Lamela Seijas

== Semantics

Semantics is based on <https://github.com/input-output-hk/marlowe/blob/stable/src/Semantics.hs>

Marlowe Contract execution is a chain of transactions,
where remaining contract and its state is passed through /Data Script/,
and actions (i.e. /Choices/ and /Oracle Values/) are passed as
/Redeemer Script/

/Validation Script/ is always the same Marlowe interpreter implementation, available below.

Both /Redeemer Script/ and /Data Script/ have the same structure:
@(Input, MarloweData)@

where

* 'Input' contains contract actions (i.e. /Pay/, /Redeem/), /Choices/ and /Oracle Values/,
* 'MarloweData' contains remaining 'Contract' and its 'State'
* 'State' is a set of 'Commit's plus a set of made 'Choice's

To spend 'TxOut' secured by Marlowe /Validator Script/, a user must provide /Redeemer Script/
that is a tuple of an 'Input' and expected output of Marlowe 'Contract' interpretation for
the given 'Input', i.e. 'Contract' and 'State'.

To ensure that user provides valid remainig 'Contract' and 'State'
Marlowe /Validator Script/ compares evaluated contract and state with provided by user,
and rejects a transaction if those don't match.

To ensure that remaining contract's /Data Script/ has the same 'Contract' and 'State'
as was passed with /Redeemer Script/, we check that /Data Script/ hash is
the same as /Redeemer Script/.
That's why those are of the same structure @(Input, MarloweData)@.

== Example

Consider simple payment contract, where Alice commits to pay 100 Ada to Bob before timeout1.
She can get back committed money if Bob didn't ask for payment before timeout2.

> let Alice = PubKey 1
> let Bob   = PubKey 2
> let timeout1 = 23
> let timeout2 = 50
> let contract = CommitCash (IdentCC 1) Alice (Value 100) timeout1 timeout2
>             (Pay (IdentPay 1) Alice Bob (Committed (IdentCC 1)) timeout2 Null)
>             Null

Alice commits:

> let input = Input (Commit (IdentCC 1) (txHash `signedBy` Alice)) [] []

Bob demands payment:

> let input = Input (Payment (IdentPay 1) (txHash `signedBy` Bob)) [] []

Or, in case Bob didn't demand payment before timeout2, Alice can require a redeem of her commit:

> let input = Input (Redeem (IdentCC 1) (txHash `signedBy` Alice)) [] []
-}

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
import           Ledger.Validation
import           LedgerBytes                (LedgerBytes (..))
import           Text.PrettyPrint.Leijen    (text)

{-# ANN module ("HLint: ignore"::String) #-}

type Timeout = Integer
type Cash = Integer

type Person = PubKey

instance Pretty PubKey where
    prettyFragment = text . show

{-|
== Identifiers

Commitments, choices and payments are all identified by identifiers.
Their types are given here. In a more sophisticated model these would
be generated automatically (and so uniquely); here we simply assume that
they are unique.

-}
newtype IdentCC = IdentCC Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

newtype IdentChoice = IdentChoice Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

newtype IdentPay = IdentPay Integer
               deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
               deriving newtype (Eq, Ord)
               deriving anyclass (Pretty)

type ConcreteChoice = Integer

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

{-| Predicate on outer world and contract 'State'.
    'interpretObservation' evaluates 'Observation' to 'Bool'
-}
data Observation = BelowTimeout Integer
            -- ^ are we still on time for something that expires on Timeout?
            | AndObs Observation Observation
            | OrObs Observation Observation
            | NotObs Observation
            | PersonChoseThis IdentChoice Person ConcreteChoice
            | PersonChoseSomething IdentChoice Person
            | ValueGE Value Value
            -- ^ is first amount is greater or equal than the second?
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
data Contract = Null
            | CommitCash IdentCC PubKey Value Timeout Timeout Contract Contract
            -- ^ commit identifier, owner, amount,
            --   start timeout, end timeout, OK contract, timed out contract
            | RedeemCC IdentCC Contract
            -- ^ commit identifier to redeem, continuation contract
            | Pay IdentPay Person Person Value Timeout Contract
            -- ^ pay identifier, from, to, amount, payment timeout,
            --   continuation (either timeout or successful payment)
            | Both Contract Contract
            -- ^ evaluate both contracts
            | Choice Observation Contract Contract
            -- ^ if observation evaluates to True evaluates first contract, second otherwise
            | When Observation Timeout Contract Contract
            -- ^ when observation evaluates to True evaluate first contract,
            --   evaluate second contract on timeout
               deriving stock (Haskell.Eq, Show, Generic)
               deriving anyclass (Pretty)

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
    State of a contract validation function.
-}
data ValidatorState = ValidatorState {
        maxCCId  :: Integer,
        maxPayId :: Integer
    }

{-|
    Internal Marlowe Contract state.
    Persisted in Data Script.
-}
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

{-|
    Contract input command.
    'Commit', 'Payment', and 'Redeem' all require a proof
    that the transaction is issued by a particular party identified with /Public Key/.
    We require 'Signature' of TxHash signed with that /Public Key/.

    E.g. if we have
    @ CommitCash ident pubKey (Value 100) ... @
    then we require
    @ Commit ident signature(pubKey) @
    to validate that transaction.
-}
data InputCommand = Commit IdentCC Signature
    | Payment IdentPay Signature
    | Redeem IdentCC Signature
    | SpendDeposit Signature
    | CreateContract
makeLift ''InputCommand

{-|
    Marlowe Contract Input.
    May contain oracle values, and newly made choices.
-}
data Input = Input InputCommand [OracleValue Integer] [Choice]

{-|
    This data type is a content of a contract's /Data Script/
-}
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

    actualMoney = Ada.toInt actualMoney'

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

{-# INLINABLE evaluateValue #-}
{-|
    Evaluates 'Value' given current block number 'Slot', oracle values, and current 'State'.
-}
evaluateValue :: Slot -> [OracleValue Integer] -> State -> Value -> Integer
evaluateValue pendingTxSlot inputOracles state value = let
    findCommit :: IdentCC -> [Commit] -> Maybe CCStatus
    findCommit i@(IdentCC searchId) commits = case commits of
        (IdentCC id, status) : _ | id == searchId -> Just status
        _ : xs                                    -> findCommit i xs
        _                                         -> Nothing

    fromOracle :: PubKey -> Slot -> [OracleValue Integer] -> Maybe Integer
    fromOracle pubKey h@(Slot blockNumber) oracles = case oracles of
        OracleValue pk (Slot bn) value : _
            | pk == pubKey && bn == blockNumber -> Just value
        _ : rest -> fromOracle pubKey h rest
        _ -> Nothing

    fromChoices :: IdentChoice -> PubKey -> [Choice] -> Maybe ConcreteChoice
    fromChoices identChoice@(IdentChoice id) pubKey choices = case choices of
        ((IdentChoice i, party), value) : _ | id == i && party == pubKey -> Just value
        _ : rest                                                         -> fromChoices identChoice pubKey rest
        _                                                                -> Nothing

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

{-# INLINABLE interpretObservation #-}
-- | Interpret 'Observation' as 'Bool'.
interpretObservation :: (State -> Value -> Integer) -> Integer -> State -> Observation -> Bool
interpretObservation evalValue blockNumber state@(State _ choices) obs = let
    find :: IdentChoice -> Person -> [Choice] -> Maybe ConcreteChoice
    find choiceId@(IdentChoice cid) person choices = case choices of
        (((IdentChoice id, party), choice) : _)
            | cid == id && party == person -> Just choice
        (_ : cs) -> find choiceId person cs
        _ -> Nothing

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
    value = Ada.toInt value'

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

    scriptInValue  = Ada.toInt scriptInValue'
    scriptOutValue = Ada.toInt scriptOutValue'

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
                (st1, res1, isValid1) = eval input state con1
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
                in case discountFromPairList from blockHeight (Ada.fromInt pv) commits of
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

        (Null, SpendDeposit sig) | null commits
            && sig `signedBy` contractCreatorPK -> (state, Null, True)

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
            That makes it easier to watch for contrac actions inside a wallet. -}
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
            SpendDeposit _ -> Ada.fromInt 0
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
