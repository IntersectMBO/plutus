{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin
    -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}

module Language.Marlowe.Common where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                       as Set
import           Prelude                        ( Show(..)
                                                , Eq(..)
                                                , Bool(..)
                                                , Ord(..)
                                                , Int
                                                , Maybe(..)
                                                , Num(..)
                                                , div
                                                )

import qualified Language.PlutusTx              as PlutusTx
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , throwOtherError
                                                , signAndSubmit
                                                , ownPubKeyTxOut
                                                )

import           Ledger                         ( DataScript(..)
                                                , Height(..)
                                                , PubKey(..)
                                                , TxOutRef'
                                                , TxOut'
                                                , TxIn'
                                                , TxOut(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                )
import qualified Ledger                         as Ledger
import           Ledger.Validation
import qualified Ledger.Validation              as Validation
import qualified Language.PlutusTx.Builtins     as Builtins
import           Language.PlutusTx.Lift         ( makeLift )
import           Language.Haskell.TH            ( Q
                                                , TExp
                                                )

type Timeout = Int
type Cash = Int

type Person      = PubKey

newtype IdentCC = IdentCC Int
               deriving (Eq, Ord, Show)



newtype IdentChoice = IdentChoice Int
               deriving (Eq, Ord, Show)


newtype IdentPay = IdentPay Int
               deriving (Eq, Ord, Show)


type ConcreteChoice = Int

type CCStatus = (Person, CCRedeemStatus)

data CCRedeemStatus = NotRedeemed Cash Timeout
               deriving (Eq, Ord, Show)


type Choice = ((IdentChoice, Person), ConcreteChoice)

type Commit = (IdentCC, CCStatus)

data Value  = Committed IdentCC
            | Value Int
            | AddValue Value Value
            | MulValue Value Value
            | DivValue Value Value Value  -- divident, divisor, default value (when divisor evaluates to 0)
            | ValueFromChoice IdentChoice Person Value
            | ValueFromOracle PubKey Value -- Oracle PubKey, default value when no Oracle Value provided
                    deriving (Eq, Show)

data Observation = BelowTimeout Int -- are we still on time for something that expires on Timeout?
                | AndObs Observation Observation
                | OrObs Observation Observation
                | NotObs Observation
                | PersonChoseThis IdentChoice Person ConcreteChoice
                | PersonChoseSomething IdentChoice Person
                | ValueGE Value Value  -- is first amount is greater or equal than the second?
                | TrueObs
                | FalseObs
                deriving (Eq, Show)


data Contract = Null
              | CommitCash IdentCC PubKey Value Timeout Timeout Contract Contract
              | RedeemCC IdentCC Contract
              | Pay IdentPay Person Person Value Timeout Contract
              | Both Contract Contract
              | Choice Observation Contract Contract
              | When Observation Timeout Contract Contract
                deriving (Eq, Show)

data ValidatorState = ValidatorState {
        ccIds  :: [IdentCC],
        payIds :: [IdentPay]
    }

data State = State {
        stateCommitted  :: [Commit],
        stateChoices :: [Choice]
    } deriving (Eq, Ord)
makeLift ''State


makeLift ''IdentCC
makeLift ''IdentChoice
makeLift ''IdentPay
makeLift ''CCRedeemStatus
makeLift ''Value
makeLift ''Observation
makeLift ''Contract
makeLift ''ValidatorState

eqValidator :: Q (TExp (ValidatorHash -> ValidatorHash -> Bool))
eqValidator = [|| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r ||]


eqIdentCC :: Q (TExp (IdentCC -> IdentCC -> Bool))
eqIdentCC = [|| \(IdentCC a) (IdentCC b) -> a == b ||]


equalValue :: Q (TExp (Value -> Value -> Bool))
equalValue = [|| \l r -> let

    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    eq l r = case (l, r) of
        (Committed idl, Committed idr) -> $$(eqIdentCC) idl idr
        (Value vl, Value vr) -> vl == vr
        (AddValue v1l v2l, AddValue v1r v2r) -> eq v1l v1r && eq v2l v2r
        (MulValue v1l v2l, MulValue v1r v2r) -> eq v1l v1r && eq v2l v2r
        (DivValue v1l v2l v3l, DivValue v1r v2r v3r) ->
            eq v1l v1r
            && eq v2l v2r
            && eq v3l v3r
        (ValueFromChoice (IdentChoice idl) pkl vl, ValueFromChoice (IdentChoice idr) pkr vr) ->
            idl == idr
            && pkl `eqPk` pkr
            && eq vl vr
        (ValueFromOracle pkl vl, ValueFromOracle pkr vr) -> pkl `eqPk` pkr && eq vl vr
        _ -> False
    in eq l r
    ||]

equalObservation :: Q (TExp ((Value -> Value -> Bool) -> Observation -> Observation -> Bool))
equalObservation = [|| \eqValue l r -> let
    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    eq :: Observation -> Observation -> Bool
    eq l r = case (l, r) of
        (BelowTimeout tl, BelowTimeout tr) -> tl == tr
        (AndObs o1l o2l, AndObs o1r o2r) -> o1l `eq` o1r && o2l `eq` o2r
        (OrObs o1l o2l, OrObs o1r o2r) -> o1l `eq` o1r && o2l `eq` o2r
        (NotObs ol, NotObs or) -> ol `eq` or
        (PersonChoseThis (IdentChoice idl) pkl cl, PersonChoseThis (IdentChoice idr) pkr cr) ->
            idl == idr && pkl `eqPk` pkr && cl == cr
        (PersonChoseSomething (IdentChoice idl) pkl, PersonChoseSomething (IdentChoice idr) pkr) ->
            idl == idr && pkl `eqPk` pkr
        (ValueGE v1l v2l, ValueGE v1r v2r) -> v1l `eqValue` v1r && v2l `eqValue` v2r
        (TrueObs, TrueObs) -> True
        (FalseObs, FalseObs) -> True
        _ -> False
    in eq l r
    ||]

equalContract :: Q (TExp ((Value -> Value -> Bool) -> (Observation -> Observation -> Bool) -> Contract -> Contract -> Bool))
equalContract = [|| \eqValue eqObservation l r -> let
    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    eq :: Contract -> Contract -> Bool
    eq l r = case (l, r) of
        (Null, Null) -> True
        (CommitCash (IdentCC idl) pkl vl t1l t2l c1l c2l, CommitCash (IdentCC idr) pkr vr t1r t2r c1r c2r) ->
            idl == idr
            && pkl `eqPk` pkr
            && vl `eqValue` vr
            && t1l == t1r && t2l == t2r
            && eq c1l c1r && eq c2l c2r
        (RedeemCC (IdentCC idl) c1l, RedeemCC (IdentCC idr) c1r) -> idl == idr && eq c1l c1r
        (Pay (IdentPay idl) pk1l pk2l vl tl cl, Pay (IdentPay idr) pk1r pk2r vr tr cr) ->
            idl == idr
            && pk1l `eqPk` pk1r
            && pk2l `eqPk` pk2r
            && vl `eqValue` vr
            && tl == tr
            && eq cl cr
        (Both c1l c2l, Both c1r c2r) -> eq c1l c1r && eq c2l c2r
        (Choice ol c1l c2l, Choice or c1r c2r) ->
            ol `eqObservation` or
            && eq c1l c1r
            && eq c2l c2r
        (When ol tl c1l c2l, When or tr c1r c2r) ->
            ol `eqObservation` or
            && tl == tr
            && eq c1l c1r
            && eq c2l c2r
        _ -> False
    in eq l r
    ||]

validateContractQ :: Q (TExp (ValidatorState -> Contract -> (ValidatorState, Bool)))
validateContractQ = [|| \state contract -> let

    notElem :: (a -> a -> Bool) -> [a] -> a -> Bool
    -- noteElem _ _ _ = False
    notElem eq as a = notel eq as a
      where
        notel eq (e : ls) a = if a `eq` e then False else notel eq ls a
        notel _ [] _ = True

    checkBoth :: ValidatorState -> Contract -> Contract -> (ValidatorState, Bool)
    checkBoth state c1 c2 = let
        (us, valid) = validate state c1
        in if valid then validate us c2
        else (state, False)

    validate :: ValidatorState -> Contract -> (ValidatorState, Bool)
    validate state@(ValidatorState ccIds payIds) contract = case contract of
        Null -> (state, True)
        CommitCash ident _ _ _ _ c1 c2 ->
            if notElem (\(IdentCC a) (IdentCC b) -> a == b) ccIds ident
            then checkBoth (ValidatorState (ident : ccIds) payIds) c1 c2
            else (state, False)
        RedeemCC _ c -> validate state c
        Pay ident _ _ _ _ c ->
            if notElem (\(IdentPay a) (IdentPay b) -> a == b) payIds ident
            then validate (ValidatorState ccIds (ident : payIds)) c
            else (state, False)
        Both c1 c2 -> checkBoth state c1 c2
        Choice _ c1 c2 -> checkBoth state c1 c2
        When _ _ c1 c2 -> checkBoth state c1 c2
    in validate state contract
    ||]

evaluateValue :: Q (TExp (Height -> [OracleValue Int] -> State -> Value -> Int))
evaluateValue = [|| \pendingTxBlockHeight inputOracles state value -> let
    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    findCommit :: IdentCC -> [(IdentCC, CCStatus)] -> Maybe CCStatus
    findCommit i@(IdentCC searchId) commits = case commits of
        (IdentCC id, status) : _ | id == searchId -> Just status
        _ : xs -> findCommit i xs
        _ -> Nothing

    fromOracle :: PubKey -> Height -> [OracleValue Int] -> Maybe Int
    fromOracle pubKey h@(Height blockNumber) oracles = case oracles of
        OracleValue pk (Height bn) value : _
            | pk `eqPk` pubKey && bn == blockNumber -> Just value
        _ : rest -> fromOracle pubKey h rest
        _ -> Nothing

    fromChoices :: IdentChoice -> PubKey -> [Choice] -> Maybe ConcreteChoice
    fromChoices identChoice@(IdentChoice id) pubKey choices = case choices of
        ((IdentChoice i, party), value) : _ | id == i && party `eqPk` pubKey -> Just value
        _ : rest -> fromChoices identChoice pubKey rest
        _ -> Nothing

    evalValue :: State -> Value -> Int
    evalValue state@(State committed choices) value = case value of
        Committed ident -> case findCommit ident committed of
            Just (_, NotRedeemed c _) -> c
            _ -> 0
        Value v -> v
        AddValue lhs rhs -> evalValue state lhs + evalValue state rhs
        MulValue lhs rhs -> evalValue state lhs * evalValue state rhs
        DivValue lhs rhs def -> do
            let divident = evalValue state lhs
            let divisor  = evalValue state rhs
            let defVal   = evalValue state def
            if divisor == 0 then defVal else divident `div` divisor
        ValueFromChoice ident pubKey def -> case fromChoices ident pubKey choices of
            Just v -> v
            _ -> evalValue state def
        ValueFromOracle pubKey def -> case fromOracle pubKey pendingTxBlockHeight inputOracles of
            Just v -> v
            _ -> evalValue state def

        in evalValue state value
    ||]

interpretObservation :: Q (TExp (
    (State -> Value -> Int)
    -> Int -> State -> Observation -> Bool))
interpretObservation = [|| \evalValue blockNumber state@(State _ choices) obs -> let
    not :: Bool -> Bool
    not = $$(PlutusTx.not)

    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    infixr 3 ||
    (||) :: Bool -> Bool -> Bool
    (||) = $$(PlutusTx.or)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    isJust :: Maybe a -> Bool
    isJust = $$(PlutusTx.isJust)

    maybe :: r -> (a -> r) -> Maybe a -> r
    maybe = $$(PlutusTx.maybe)

    find :: IdentChoice -> Person -> [Choice] -> Maybe ConcreteChoice
    find choiceId@(IdentChoice cid) (person) choices = case choices of
        (((IdentChoice id, party), choice) : _)
            | cid == id && party `eqPk` person -> Just choice
        (_ : cs) -> find choiceId person cs
        _ -> Nothing

    go :: Observation -> Bool
    go obs = case obs of
        BelowTimeout n -> blockNumber <= n
        AndObs obs1 obs2 -> go obs1 && go obs2
        OrObs obs1 obs2 -> go obs1 || go obs2
        NotObs obs -> not (go obs)
        PersonChoseThis choiceId person referenceChoice ->
            maybe False (== referenceChoice) (find choiceId person choices)
        PersonChoseSomething choiceId person -> isJust (find choiceId person choices)
        ValueGE a b -> evalValue state a >= evalValue state b
        TrueObs -> True
        FalseObs -> False
    in go obs
    ||]
