{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
module Language.Marlowe.Analysis.FSSemantics where

import           Control.Monad
import           Data.Foldable              (fold)
import           Data.List                  (foldl')
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.SBV
import           Data.SBV.Internals         (SMTModel (..))
import qualified Data.Set                   as S
import           Language.Marlowe.Semantics
import qualified Language.PlutusTx.AssocMap as AssocMap
import qualified Language.PlutusTx.Ratio    as P
import           Ledger                     (Slot (..))

---------------------------------------------------
-- Static analysis logic and symbolic operations --
---------------------------------------------------

-- Symbolic version of Input (with symbolic value but concrete identifiers)
data SymInput = SymDeposit AccountId Party Token SInteger
              | SymChoice ChoiceId SInteger
              | SymNotify deriving (Show)

-- Symbolic version of State:
-- We keep as much things concrete as possible.
-- In addition to normal State information we also store symbolic values that
-- represent the symbolic trace we are evaluating (the way we got to the current
-- part of the contract).
--
-- Symbolic trace is composed of:
--
-- *** Current transaction info
-- lowSlot, highSlot -- slot interval for the most recent transaction
-- symInput -- input for the most recent transaction
-- whenPos -- position in the When for the most recen transaction (see trace and paramTrace)
--
-- *** Previous transaction info
-- traces -- symbolic information about previous transactions (when we reach a When we
--           consider adding the current transaction to this list)
--           first integer is lowSlot, second is highSlot, last integer is the position in
--           the When (which case of the When the input corresponds to 0 is timeout)
-- *** Input parameter transaction info
-- paramTrace -- this is actually an input parameter, we get it as input for the SBV
--               property and we constrain it to match traces for any of the executions,
--               SBV will try to find a paramTrace that matches, and that will be the
--               solution to the analysis (the counterexample if any). It has a fixed
--               length that is calculated as the maximum bound given by countWhens,
--               which is the maximum number of transactions that are necessary to explore
--               the whole contract. This bound is proven in TransactionBound.thy
--
-- The rest of the symbolic state just corresponds directly to State with symbolic values:
-- symAccounts, symChoices, and symBoundValues
--
-- minSlot just corresponds to lowSlot, because it is just a lower bound for the minimum
-- slot, and it gets updated with the minimum slot.
data SymState = SymState { lowSlot        :: SInteger
                         , highSlot       :: SInteger
                         , traces         :: [(SInteger, SInteger, Maybe SymInput, Integer)]
                         , paramTrace     :: [(SInteger, SInteger, SInteger, SInteger)]
                         , symInput       :: Maybe SymInput
                         , whenPos        :: Integer
                         , symAccounts    :: Map (AccountId, Token) SInteger
                         , symChoices     :: Map ChoiceId SInteger
                         , symBoundValues :: Map ValueId SInteger
                         , symFFICalls    :: Map Integer SInteger
                         } deriving (Show)

data CounterExample = MkCounterExample
    { ceInitialSlot       :: Slot
    , ceTransactionInputs :: [TransactionInput]
    , ceWarnings          :: [TransactionWarning]
    , ceFFIValues         :: FFIValues
    }
  deriving (Show)

data AnalysisResult = ValidContract
                    | CounterExample CounterExample
                    | AnalysisError String
  deriving (Show)


isContractValid :: AnalysisResult -> Bool
isContractValid ValidContract = True
isContractValid _             = False


-- It generates a valid symbolic interval with lower bound ms (if provided)
generateSymbolicInterval :: Maybe Integer -> Symbolic (SInteger, SInteger)
generateSymbolicInterval Nothing =
  do hs <- sInteger_
     ls <- sInteger_
     constrain (ls .<= hs)
     return (ls, hs)
generateSymbolicInterval (Just ms) =
  do i@(ls, _) <- generateSymbolicInterval Nothing
     constrain (ls .>= literal ms)
     return i


-- foldWithKey for Plutus' AssocMap
foldAssocMapWithKey :: (a -> k -> b -> a) -> a -> AssocMap.Map k b -> a
foldAssocMapWithKey f acc = foldl' decF acc . AssocMap.toList
  where decF a (k, v) = f a k v


-- Convert Plutus' AssocMap into a Map with symbolic values, which are literals of
-- the content of the original AssocMap
toSymMap :: Ord k => SymVal v => AssocMap.Map k v -> Map k (SBV v)
toSymMap = foldAssocMapWithKey toSymItem mempty
  where toSymItem :: Ord k => SymVal v => Map k (SBV v) -> k -> v -> Map k (SBV v)
        toSymItem acc k v = M.insert k (literal v) acc


foldMapContract :: Monoid m
    => (Contract -> m)
    -> (Case Contract -> m)
    -> (Observation -> m)
    -> (Value Observation -> m)
    -> Contract -> m
foldMapContract fcont fcase fobs fvalue contract = case contract of
    Close                -> evaledContract
    Pay _ _ _ value cont -> evaledContract <> fvalue' value <> go cont
    If obs cont1 cont2   -> evaledContract <> fobs' obs <> go cont1 <> go cont2
    When cases _ cont    -> evaledContract <> foldMap fcase' cases <> go cont
    Let _ value cont     -> evaledContract <> fvalue value <> go cont
    Assert obs cont      -> evaledContract <> fobs' obs <> go cont
  where
    evaledContract = fcont contract
    go = foldMapContract fcont fcase fobs fvalue
    fcase' cs@(Case _ cont) = fcase cs <> go cont
    fobs' obs = case obs of
        AndObs a b  -> fobs obs <> fobs' a <> fobs' b
        OrObs  a b  -> fobs obs <> fobs' a <> fobs' b
        NotObs a    -> fobs obs <> fobs' a
        ValueGE a b -> fobs obs <> fvalue' a <> fvalue' b
        ValueGT a b -> fobs obs <> fvalue' a <> fvalue' b
        ValueLT a b -> fobs obs <> fvalue' a <> fvalue' b
        ValueLE a b -> fobs obs <> fvalue' a <> fvalue' b
        ValueEQ a b -> fobs obs <> fvalue' a <> fvalue' b
        _           -> fobs obs
    fvalue' v = case v of
        NegValue val -> fvalue v <> fvalue' val
        AddValue a b -> fvalue v <> fvalue' a <> fvalue' b
        SubValue a b -> fvalue v <> fvalue' a <> fvalue' b
        MulValue a b -> fvalue v <> fvalue' a <> fvalue' b
        Scale _ val  -> fvalue v <> fvalue' val
        Cond obs a b -> fvalue v <> fobs' obs <> fvalue' a <> fvalue' b
        _            -> fvalue v

foldMapContractValue :: Monoid m => (Value Observation -> m) -> Contract -> m
foldMapContractValue = foldMapContract (const mempty) (const mempty) (const mempty)


initFFICalls :: MarloweFFIInfo -> Contract -> Symbolic (Map Integer SInteger)
initFFICalls MarloweFFIInfo{unMarloweFFIInfo} contract = do
    let calls = foldMapContractValue collectFFICalls contract
    foldM createSymbolicInputForFFICall mempty calls
  where
    collectFFICalls (Call name _) = S.singleton name
    collectFFICalls _             = mempty

    createSymbolicInputForFFICall m name = case AssocMap.lookup name unMarloweFFIInfo of
        Just FFInfo{ffiRangeBounds, ffiOutOfBoundsValue} -> do
            value <- sInteger ("call_" ++ show name)
            constrain $ ensureBounds value ffiRangeBounds .|| value .== literal ffiOutOfBoundsValue
            return $ M.insert name value m
        Nothing ->
            -- a Call name that is not in MarloweFFIInfo always evaluates to 0
            return $ M.insert name (literal 0) m


-- Create initial symbolic state, it takes an optional concrete State to serve
-- as initial state, this way analysis can be done from a half-executed contract.
-- First parameter (paramTrace) is the input parameter trace, which is just a fixed length
-- list of symbolic integers that are matched to trace.
-- When Nothing is passed as second parameter it acts like emptyState.
mkInitialSymState :: MarloweFFIInfo -> [(SInteger, SInteger, SInteger, SInteger)] -> Contract -> Maybe State
                  -> Symbolic SymState
mkInitialSymState ffi paramTrace contract Nothing = do
    (ls, hs) <- generateSymbolicInterval Nothing
    ffiCalls <- initFFICalls ffi contract
    return $ SymState { lowSlot = ls
                      , highSlot = hs
                      , traces = []
                      , paramTrace = paramTrace
                      , symInput = Nothing
                      , whenPos = 0
                      , symAccounts = mempty
                      , symChoices = mempty
                      , symBoundValues = mempty
                      , symFFICalls = ffiCalls }
mkInitialSymState ffi paramTrace contract (Just State{accounts, choices, boundValues, minSlot}) = do
    (ls, hs) <- generateSymbolicInterval (Just (getSlot minSlot))
    ffiCalls <- initFFICalls ffi contract
    return $ SymState { lowSlot = ls
                      , highSlot = hs
                      , traces = []
                      , paramTrace = paramTrace
                      , symInput = Nothing
                      , whenPos = 0
                      , symAccounts = toSymMap accounts
                      , symChoices = toSymMap choices
                      , symBoundValues = toSymMap boundValues
                      , symFFICalls = ffiCalls }


-- It converts a symbolic trace into a list of 4-uples of symbolic integers,
-- this is a minimalistic representation of the counter-example trace that aims
-- to minimise the functionalities from SBV that we use (just integers) for efficiency.
-- The integers in the tuple represent:
-- 1st - slot interval min slot
-- 2nd - slot interval max slot
-- 3rd - When clause used (0 for timeout branch)
-- 4rd - Symbolic value (money in deposit, chosen value in choice)
--
-- Because the param trace has fixed length we fill the unused transactions with -1,
-- these are pruned after analysis.
--
-- The identifiers for Deposit and Choice are calculated using the When clause and
-- the contract (which is concrete), and using the semantics after a counter example is
-- found.
convertToSymbolicTrace :: [(SInteger, SInteger, Maybe SymInput, Integer)] ->
                          [(SInteger, SInteger, SInteger, SInteger)] -> SBool
convertToSymbolicTrace [] [] = sTrue
convertToSymbolicTrace [] ((a, b, c, d):t) = (a .== -1) .&& (b .== -1) .&& (c .== -1) .&&
                                             (d .== -1) .&& convertToSymbolicTrace [] t
convertToSymbolicTrace ((lowS, highS, inp, pos):t) ((a, b, c, d):t2) =
  (lowS .== a) .&& (highS .== b) .&& (getSymValFrom inp .== c) .&& (literal pos .== d) .&&
  convertToSymbolicTrace t t2
  where
    getSymValFrom :: Maybe SymInput -> SInteger
    getSymValFrom Nothing                       = 0
    getSymValFrom (Just (SymDeposit _ _ _ val)) = val
    getSymValFrom (Just (SymChoice _ val))      = val
    getSymValFrom (Just SymNotify)              = 0
convertToSymbolicTrace _ _ = error "Provided symbolic trace is not long enough"


-- Symbolic version evalValue
symEvalVal :: Value Observation -> SymState -> SInteger
symEvalVal (AvailableMoney accId tok) symState =
  M.findWithDefault (literal 0) (accId, tok) (symAccounts symState)
symEvalVal (Constant inte) symState = literal inte
symEvalVal (NegValue val) symState = - symEvalVal val symState
symEvalVal (AddValue lhs rhs) symState = symEvalVal lhs symState +
                                         symEvalVal rhs symState
symEvalVal (SubValue lhs rhs) symState = symEvalVal lhs symState -
                                         symEvalVal rhs symState
symEvalVal (MulValue lhs rhs) symState = symEvalVal lhs symState *
                                         symEvalVal rhs symState
symEvalVal (Scale s rhs) symState =
  let (n, d) = (P.numerator s, P.denominator s)
      nn = symEvalVal rhs symState * literal n
      (q, r) = nn `sQuotRem` literal d in
  ite (abs r * 2 .< literal (abs d)) q (q + signum nn * literal (signum d))
symEvalVal (ChoiceValue choId) symState =
  M.findWithDefault (literal 0) choId (symChoices symState)
symEvalVal SlotIntervalStart symState = lowSlot symState
symEvalVal SlotIntervalEnd symState = highSlot symState
symEvalVal (UseValue valId) symState =
  M.findWithDefault (literal 0) valId (symBoundValues symState)
symEvalVal (Cond cond v1 v2) symState = ite (symEvalObs cond symState)
                                            (symEvalVal v1 symState)
                                            (symEvalVal v2 symState)
symEvalVal (Call name _) symState =
  M.findWithDefault (literal 0) name (symFFICalls symState)


-- Symbolic version evalObservation
symEvalObs :: Observation -> SymState -> SBool
symEvalObs (AndObs obs1 obs2) symState = symEvalObs obs1 symState .&&
                                         symEvalObs obs2 symState
symEvalObs (OrObs obs1 obs2) symState = symEvalObs obs1 symState .||
                                        symEvalObs obs2 symState
symEvalObs (NotObs obs) symState = sNot $ symEvalObs obs symState
symEvalObs (ChoseSomething choiceId) symState =
  literal (M.member choiceId (symChoices symState))
symEvalObs (ValueGE lhs rhs) symState = symEvalVal lhs symState .>=
                                        symEvalVal rhs symState
symEvalObs (ValueGT lhs rhs) symState = symEvalVal lhs symState .>
                                        symEvalVal rhs symState
symEvalObs (ValueLT lhs rhs) symState = symEvalVal lhs symState .<
                                        symEvalVal rhs symState
symEvalObs (ValueLE lhs rhs) symState = symEvalVal lhs symState .<=
                                        symEvalVal rhs symState
symEvalObs (ValueEQ lhs rhs) symState = symEvalVal lhs symState .==
                                        symEvalVal rhs symState
symEvalObs TrueObs _ = sTrue
symEvalObs FalseObs _ = sFalse


-- Update the symbolic state given a symbolic input (just the maps)
updateSymInput :: Maybe SymInput -> SymState -> Symbolic SymState
updateSymInput Nothing symState = return symState
updateSymInput (Just (SymDeposit accId _ tok val)) symState =
  let resultVal = M.findWithDefault 0 (accId, tok) (symAccounts symState)
                   + smax (literal 0) val in
  return (symState {symAccounts =
                       M.insert (accId, tok) resultVal
                                (symAccounts symState)})
updateSymInput (Just (SymChoice choId val)) symState =
  return (symState {symChoices = M.insert choId val (symChoices symState)})
updateSymInput (Just SymNotify) symState = return symState


-- Moves the current transaction to the list of transactions and creates a
-- new one. It takes newLowSlot and newHighSlot as parameters because the
-- values and observations are evaluated using those, so we cannot just generate
-- them here (they are linked to the SymInput (3rd parameter).
-- If SymInput is Nothing it means the transaction went to timeout.
-- If the transaction didn't go to timeout, we know the new transaction has maxSlot smaller
-- than timeout. If it went to timeout we know the new transaction has minSlot greater or
-- equal than timeout. We also need to check previous transaction does not have ambiguous
-- interval with the current When, because that would mean the transaction is invalid.
-- In the case of timeout it is possible we don't actually need a new transaction,
-- we can reuse the previous transaction, we model this by allowing both low and high
-- slot to be equal to the ones of the previous transaction. That will typically make one
-- of the transactions useless, but we discard useless transactions by the end so that
-- is fine.
addTransaction :: SInteger -> SInteger -> Maybe SymInput -> Timeout -> SymState -> Integer
               -> Symbolic (SBool, SymState)
addTransaction newLowSlot newHighSlot Nothing slotTim
               symState@SymState { lowSlot = oldLowSlot
                                 , highSlot = oldHighSlot
                                 , traces = oldTraces
                                 , symInput = prevSymInp
                                 , whenPos = oldPos } pos =
  do let tim = getSlot slotTim
     constrain (newLowSlot .<= newHighSlot)
     let conditions = ((oldHighSlot .< literal tim) .||
                      ((oldLowSlot .== newLowSlot) .&& (oldHighSlot .== newHighSlot))) .&&
                      (newLowSlot .>= literal tim)
     uSymInput <- updateSymInput Nothing
                                 (symState { lowSlot = newLowSlot
                                           , highSlot = newHighSlot
                                           , traces = (oldLowSlot, oldHighSlot,
                                                       prevSymInp, oldPos):oldTraces
                                           , symInput = Nothing
                                           , whenPos = pos })
     return (conditions, uSymInput)
addTransaction newLowSlot newHighSlot newSymInput slotTim
               symState@SymState { lowSlot = oldLowSlot
                                 , highSlot = oldHighSlot
                                 , traces = oldTraces
                                 , symInput = prevSymInp
                                 , whenPos = oldPos } pos =
  do let tim = getSlot slotTim
     constrain (newLowSlot .<= newHighSlot)
     let conditions = (oldHighSlot .< literal tim) .&&
                      (newHighSlot .< literal tim) .&&
                      (newLowSlot .>= oldLowSlot)
     uSymInput <- updateSymInput newSymInput
                        (symState { lowSlot = newLowSlot
                                  , highSlot = newHighSlot
                                  , traces = (oldLowSlot, oldHighSlot, prevSymInp, oldPos)
                                             :oldTraces
                                  , symInput = newSymInput
                                  , whenPos = pos })
     return (conditions, uSymInput)


-- It only "or"s the first symbolic boolean to the second one if the
-- concrete boolean is False, otherwise it just passes the second
-- symbolic parameter through
onlyAssertionsPatch :: Bool -> SBool -> SBool -> SBool
onlyAssertionsPatch b p1 p2 = if b then p2 else p1 .|| p2


-- This is the main static analysis loop for contracts.
-- - oa -- indicates whether we want to report only failing assertions (not any warning)
-- - hasErr -- indicates whether the current symbolic execution has already
-- raised a warning (this is a necessary condition for it to be a counter-example)
-- - contract -- remaining contract
-- - sState -- symbolic state
--
-- The result of this function is a boolean that indicates whether:
-- 1. The transaction is valid (according to the semantics)
-- 2. It has issued a warning (as indicated by hasErr)
isValidAndFailsAux :: Bool -> SBool -> Contract -> SymState
                   -> Symbolic SBool
isValidAndFailsAux oa hasErr contract sState = case contract of
    Close -> return (hasErr .&& whatTheHellIsThis)
      where
        whatTheHellIsThis = convertToSymbolicTrace newTraces (paramTrace sState)
        newTraces = (lowSlot sState, highSlot sState, symInput sState, whenPos sState) : traces sState

    Pay accId payee token val cont -> isValidAndFailsAux oa newHasError cont finalSState
      where
        concVal = symEvalVal val sState
        originalMoney = M.findWithDefault 0 (accId, token) (symAccounts sState)
        remainingMoneyInAccount = originalMoney - smax (literal 0) concVal
        newAccs = M.insert (accId, token) (smax (literal 0) remainingMoneyInAccount)
                                                    (symAccounts sState)
        newAccs' = case payee of
                Account destAccId ->
                    M.insert (destAccId, token)
                            (smin originalMoney (smax (literal 0) concVal)
                                + M.findWithDefault 0 (destAccId, token) newAccs)
                            newAccs
                _ -> newAccs
        finalSState = sState { symAccounts = newAccs' }
        newHasError = onlyAssertionsPatch
                              oa
                              ((remainingMoneyInAccount .< 0) -- Partial payment
                               .|| (concVal .<= 0)) -- Non-positive payment
                              hasErr

    If obs cont1 cont2 -> do
        let obsVal = symEvalObs obs sState
        contVal1 <- isValidAndFailsAux oa hasErr cont1 sState
        contVal2 <- isValidAndFailsAux oa hasErr cont2 sState
        return (ite obsVal contVal1 contVal2)

    When list timeout cont ->
        isValidAndFailsWhen oa hasErr list timeout cont (const $ const sFalse) sState 1

    Let valId val cont -> do
        let concVal = symEvalVal val sState
        let newBVMap = M.insert valId concVal (symBoundValues sState)
        let newSState = sState { symBoundValues = newBVMap }
        let newHasError = onlyAssertionsPatch
                              oa
                              (literal (M.member valId (symBoundValues sState))) -- Shadowed definition
                              hasErr
        isValidAndFailsAux oa newHasError cont newSState

    Assert obs cont -> isValidAndFailsAux oa (hasErr .|| sNot obsVal) cont sState
      where obsVal = symEvalObs obs sState


-- Returns sTrue iif the given sinteger is in the list of bounds
ensureBounds :: SInteger -> [Bound] -> SBool
ensureBounds _ [] = sFalse
ensureBounds symVal (Bound lowBnd hiBnd : t) =
    ((symVal .>= literal lowBnd) .&& (symVal .<= literal hiBnd)) .|| ensureBounds symVal t


-- Just combines addTransaction and isValidAndFailsAux
applyInputConditions :: Bool -> SInteger -> SInteger -> SBool -> Maybe SymInput -> Timeout
                     -> SymState -> Integer -> Contract
                     -> Symbolic (SBool, SBool)
applyInputConditions oa ls hs hasErr maybeSymInput timeout sState pos cont =
  do (newCond, newSState) <- addTransaction ls hs maybeSymInput timeout sState pos
     newTrace <- isValidAndFailsAux oa hasErr cont newSState
     return (newCond, newTrace)


-- Generates two new slot numbers and puts them in the symbolic state
addFreshSlotsToState :: SymState -> Symbolic (SInteger, SInteger, SymState)
addFreshSlotsToState sState =
  do newLowSlot <- sInteger_
     newHighSlot <- sInteger_
     return (newLowSlot, newHighSlot, sState {lowSlot = newLowSlot, highSlot = newHighSlot})


-- Analysis loop for When construct. Essentially, it iterates over all the cases and
-- branches the static analysis. All parameters are the same as isValidAndFailsAux except
-- for previousMatch and pos:
-- - previousMatch - Is a function that tells whether some previous case has matched, if
-- that happened then the current case would never be reached, we keep adding conditions
-- to the function and pass it to the next iteration of isValidAndFailsWhen.
-- - pos - Is the position of the current Case clause [1..], 0 means timeout branch.
isValidAndFailsWhen :: Bool -> SBool -> [Case Contract] -> Timeout -> Contract -> (SymInput -> SymState -> SBool)
                    -> SymState -> Integer -> Symbolic SBool
isValidAndFailsWhen oa hasErr [] timeout cont previousMatch sState pos =
  do newLowSlot <- sInteger_
     newHighSlot <- sInteger_
     (cond, newTrace)
               <- applyInputConditions oa newLowSlot newHighSlot
                                       hasErr Nothing timeout sState 0 cont
     return (ite cond newTrace sFalse)
isValidAndFailsWhen oa hasErr (Case (Deposit accId party token val) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowSlot, newHighSlot, sStateWithInput) <- addFreshSlotsToState sState
     let concVal = symEvalVal val sStateWithInput
     let symInput = SymDeposit accId party token concVal
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           let pmConcVal = symEvalVal val pmSymState in
           case otherSymInput of
             SymDeposit otherAccId otherParty otherToken otherConcVal ->
               if (otherAccId == accId) && (otherParty == party)
                  && (otherToken == token)
               then (otherConcVal .== pmConcVal) .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState
     (newCond, newTrace)
               <- applyInputConditions oa newLowSlot newHighSlot
                      (onlyAssertionsPatch oa
                                           (concVal .<= 0) -- Non-positive deposit warning
                                           hasErr)
                      (Just symInput) timeout sState pos cont
     contTrace <- isValidAndFailsWhen oa hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& sNot clashResult) newTrace contTrace)
isValidAndFailsWhen oa hasErr (Case (Choice choId bnds) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowSlot, newHighSlot, sStateWithInput) <- addFreshSlotsToState sState
     concVal <- sInteger_
     let symInput = SymChoice choId concVal
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           case otherSymInput of
             SymChoice otherChoId otherConcVal ->
               if otherChoId == choId
               then ensureBounds otherConcVal bnds .|| previousMatch otherSymInput pmSymState
               else previousMatch otherSymInput pmSymState
             _ -> previousMatch otherSymInput pmSymState
     contTrace <- isValidAndFailsWhen oa hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     (newCond, newTrace)
               <- applyInputConditions oa newLowSlot newHighSlot
                                       hasErr (Just symInput) timeout sState pos cont
     return (ite (newCond .&& sNot clashResult)
                 (ensureBounds concVal bnds .&& newTrace)
                 contTrace)
isValidAndFailsWhen oa hasErr (Case (Notify obs) cont:rest)
                    timeout timCont previousMatch sState pos =
  do (newLowSlot, newHighSlot, sStateWithInput) <- addFreshSlotsToState sState
     let obsRes = symEvalObs obs sStateWithInput
     let symInput = SymNotify
     let clashResult = previousMatch symInput sStateWithInput
     let newPreviousMatch otherSymInput pmSymState =
           let pmObsRes = symEvalObs obs pmSymState in
           case otherSymInput of
             SymNotify -> pmObsRes .|| previousMatch otherSymInput pmSymState
             _         -> previousMatch otherSymInput pmSymState
     contTrace <- isValidAndFailsWhen oa hasErr rest timeout timCont
                                      newPreviousMatch sState (pos + 1)
     (newCond, newTrace)
               <- applyInputConditions oa newLowSlot newHighSlot
                                       hasErr (Just symInput) timeout sState pos cont
     return (ite (newCond .&& obsRes .&& sNot clashResult) newTrace contTrace)


--------------------------------------------------
-- Wrapper - SBV handling and result extraction --
--------------------------------------------------

-- Counts the maximum number of nested Whens. This acts as a bound for the maximum
-- necessary number of transactions for exploring the whole contract. This bound
-- has been proven in TransactionBound.thy
countWhens :: Contract -> Integer
countWhens contract = case contract of
    Close             -> 0
    Pay uv uw ux uy c -> countWhens c
    If uz c c2        -> max (countWhens c) (countWhens c2)
    When cl t c       -> 1 + max (countWhensCaseList cl) (countWhens c)
    Let va vb c       -> countWhens c
    Assert o c        -> countWhens c
  where
    countWhensCaseList :: [Case Contract] -> Integer
    countWhensCaseList (Case uu c : tail) = max (countWhens c) (countWhensCaseList tail)
    countWhensCaseList []                 = 0


-- Main wrapper of the static analysis takes a Bool that indicates whether only
-- assertions should be checked, a Contract, a paramTrace, and an optional
-- State. paramTrace is actually an output parameter. We do not put it in the result of
-- this function because then we would have to return a symbolic list that would make
-- the whole process slower. It is meant to be used just with SBV, with a symbolic
-- paramTrace, and we use the symbolic paramTrace to know which is the counterexample.
contractIsGood :: Bool -> MarloweFFIInfo -> Contract -> [(SInteger, SInteger, SInteger, SInteger)] -> Maybe State
        -> Symbolic SBool
contractIsGood oa ffi contract st maybeState = do
    ess <- mkInitialSymState ffi st contract maybeState
    isValidAndFailsAux oa sFalse contract ess


-- It generates a list of variable names for the variables that conform paramTrace.
-- The list will account for the given number of transactions (four vars per transaction).
generateLabels :: Integer -> [Labels]
generateLabels n = foldMap genLabels [1..n]
  where
    genLabels :: Integer -> [Labels]
    genLabels n = [(action_label ++ "minSlot",
                    action_label ++ "maxSlot",
                    action_label ++ "value",
                    action_label ++ "branch")]
      where action_label = "action_" ++ show n ++ "_"


-- Takes a list of variable names for the paramTrace and generates the list of symbolic
-- variables. It returns the list of symbolic variables generated (list of 4-uples).
generateParameters :: [Labels] -> Symbolic [(SInteger, SInteger, SInteger, SInteger)]
generateParameters labels = forM labels $ \(sl, sh, v, b) -> do
    isl <- sInteger sl
    ish <- sInteger sh
    iv <- sInteger v
    ib <- sInteger b
    return (isl, ish, iv, ib)


-- Takes the list of paramTrace variable names and the list of mappings of these
-- names to concrete values, and reconstructs a concrete list of 4-uples of the ordered
-- concrete values.
makeTraceInputs :: [Labels] -> Map String Integer -> [TraceInput]
makeTraceInputs ((sl, sh, v, b) : t) mappings =
    if ib == -1 then []
    else (isl, ish, iv, ib) : makeTraceInputs t mappings
  where (Just isl) = M.lookup sl mappings
        (Just ish) = M.lookup sh mappings
        (Just iv) = M.lookup v mappings
        (Just ib) = M.lookup b mappings
makeTraceInputs [] _ = []


-- Reconstructs an input from a Case list a Case position and a value (deposit amount or
-- chosen value)
caseToInput :: [Case a] -> Integer -> Integer -> Input
caseToInput [] _ _ = error "Wrong number of cases interpreting result"
caseToInput (Case h _:t) c v
  | c > 1 = caseToInput t (c - 1) v
  | c == 1 = case h of
               Deposit accId party tok _ -> IDeposit accId party tok v
               Choice choId _            -> IChoice choId v
               Notify _                  -> INotify
  | otherwise = error "Negative case number"


-- Given an input, state, and contract, it runs the semantics on the transaction,
-- and it adds the transaction and warnings issued to the result as long as the
-- transaction was not useless. It assumes the transaction is either valid or useless,
-- other errors would mean the counterexample is not valid.
-- Input is passed as a combination and function from input list to transaction input and
-- input list for convenience. The list of 4-tuples is passed through because it is used
-- to recursively call executeAndInterpret (co-recursive funtion).
computeAndContinue :: MarloweFFI -> TransactionInput -> State -> Contract
                   -> [TraceInput]
                   -> [([TransactionInput], [TransactionWarning])]
computeAndContinue ffi transactionInput state contract trace =
  case computeTransaction ffi transactionInput state contract of
    Error TEUselessTransaction -> executeAndInterpret ffi state trace contract
    TransactionOutput { txOutWarnings = warnings
                      , txOutState = newState
                      , txOutContract = newContract}
                          -> ([transactionInput], warnings)
                             :executeAndInterpret ffi newState trace newContract


-- Takes a list of 4-uples (and state and contract) and interprets it as a list of
-- transactions and also computes the resulting list of warnings.
executeAndInterpret :: MarloweFFI -> State -> [TraceInput] -> Contract
                    -> [([TransactionInput], [TransactionWarning])]
executeAndInterpret _ _ [] _ = []
executeAndInterpret ffi state ((l, h, v, branch):trace) cont
  | branch == 0 = computeAndContinue ffi (mkTransactionInput []) state cont trace
  | otherwise = case reduceContractUntilQuiescent env state cont of
        ContractQuiescent _ _ _ tempCont ->
            case tempCont of
                When cases _ _ -> computeAndContinue
                                    ffi
                                    (mkTransactionInput [caseToInput cases branch v])
                                    state
                                    cont
                                    trace
                _ -> error "Cannot interpret result"
        _ -> error "Error reducing contract when interpreting result"
  where
    mySlotInterval = (Slot l, Slot h)
    env = Environment { slotInterval = mySlotInterval, marloweFFI = ffi }
    mkTransactionInput inputs = TransactionInput { txInterval = mySlotInterval, txInputs = inputs }


-- It wraps executeAndInterpret so that it takes an optional State, and also
-- combines the results of executeAndInterpret in one single tuple.
interpretResult :: MarloweFFIInfo -> FFIValues -> [TraceInput] -> Contract -> Maybe State
                -> CounterExample
interpretResult _ _ [] _ _ = error "Empty result"
interpretResult ffiInfo ffiValues trace@((l, _, _, _):_) contract maybeState =
    MkCounterExample { ceInitialSlot = Slot l
                     , ceTransactionInputs = txInputs
                     , ceWarnings = warnings
                     , ceFFIValues = ffiValues
                     }
  where
    (txInputs, warnings) = fold $ executeAndInterpret ffi initialState trace contract

    initialState = case maybeState of
        Nothing -> emptyState (Slot l)
        Just x  -> x

    ffi = ffiFromFFIInfo ffiInfo ffiValues

    ffiFromFFIInfo :: MarloweFFIInfo -> FFIValues -> MarloweFFI
    ffiFromFFIInfo MarloweFFIInfo{unMarloweFFIInfo} ffiValues = MarloweFFI (AssocMap.fromList list)
      where
        list = fmap convertFFIInfoToMarloweFFI $ AssocMap.toList unMarloweFFIInfo

        convertFFIInfoToMarloweFFI (name, ffinfo) = case M.lookup name ffiValues of
            Just value -> (name, (\state contract args -> value, ffinfo))
            Nothing    -> error $ "Cannot find FFI call value for " <> show name


type Labels = (String, String, String, String)
type TraceInput = (Integer, Integer, Integer, Integer)
type FFIValues = Map Integer Integer

-- It interprets the counter example found by SBV (SMTModel), given the contract,
-- and initial state (optional), and the list of variables used.
extractCounterExample :: MarloweFFIInfo -> SMTModel -> Contract -> Maybe State -> [Labels]
                      -> CounterExample
extractCounterExample ffi@MarloweFFIInfo{unMarloweFFIInfo} smtModel cont maybeState labels = counterExample
  where paramValues = M.fromList (map (\(a, b) -> (a, fromCV b :: Integer)) $ modelAssocs smtModel)
        traceInputs = reverse $ makeTraceInputs labels paramValues
        ffiValues = foldMap collectFFIValues $ AssocMap.toList unMarloweFFIInfo
          where
            collectFFIValues (name, _) =
                case M.lookup ("call_" <> show name) paramValues of
                    Just value -> M.singleton name value
                    Nothing    -> error $ "Unknown FFI call name: " <> show name
        counterExample = interpretResult ffi ffiValues traceInputs cont maybeState


-- Wrapper function that carries the static analysis and interprets the result.
-- It generates variables, runs SBV, and it interprets the result in Marlowe terms.
warningsTraceCustom :: MarloweFFIInfo -> Bool
              -> Contract
              -> Maybe State
              -> IO AnalysisResult
warningsTraceCustom ffi onlyAssertions contract maybeState = do
    thmRes@(ThmResult result) <- proveWith z3 counterExampleExists
    case result of
        Unsatisfiable _ _ -> return ValidContract
        Satisfiable _ smtModel -> do
            let counterExample = extractCounterExample ffi smtModel contract maybeState labels
            return $ CounterExample counterExample
        _ -> return $ AnalysisError (show thmRes)
  where
    maxActs = 1 + countWhens contract
    labels = generateLabels maxActs
    counterExampleExists = do
        params <- generateParameters labels
        good <- contractIsGood onlyAssertions ffi contract params maybeState
        return (sNot good)


-- Like warningsTraceCustom but checks all warnings (including assertions)
warningsTraceWithState :: MarloweFFIInfo -> Contract
              -> Maybe State
              -> IO AnalysisResult
warningsTraceWithState ffi = warningsTraceCustom ffi False


-- Like warningsTraceCustom but only checks assertions.
onlyAssertionsWithState :: MarloweFFIInfo -> Contract
              -> Maybe State
              -> IO AnalysisResult
onlyAssertionsWithState ffi = warningsTraceCustom ffi True


-- Like warningsTraceWithState but without initialState.
warningsTrace :: MarloweFFIInfo -> Contract
              -> IO AnalysisResult
warningsTrace ffi con = warningsTraceWithState ffi con Nothing
