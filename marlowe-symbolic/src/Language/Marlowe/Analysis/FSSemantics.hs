module Language.Marlowe.Analysis.FSSemantics where

import           Data.List                  (foldl', genericIndex)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as M
import           Data.Maybe                 (isNothing)
import           Data.SBV
import qualified Data.SBV.Either            as SE
import           Data.SBV.Internals         (SMTModel (..))
import qualified Data.SBV.List              as SL
import qualified Data.SBV.Maybe             as SM
import qualified Data.SBV.Tuple             as ST
import           Data.Set                   (Set)
import qualified Data.Set                   as S
import           Language.Marlowe.Semantics
import qualified Language.PlutusTx.AssocMap as AssocMap
import           Ledger                     (Slot (..))

data SymInput = SymDeposit AccountId Party Token SInteger
              | SymChoice ChoiceId SInteger
              | SymNotify

data SymState = SymState { lowSlot        :: SInteger
                         , highSlot       :: SInteger
                         , traces         :: [(SInteger, SInteger, Maybe SymInput, Integer)]
                         , paramTrace     :: [(SInteger, SInteger, SInteger, SInteger)]
                         , symAccounts    :: Map (AccountId, Token) SInteger
                         , symChoices     :: Map ChoiceId SInteger
                         , symBoundValues :: Map ValueId SInteger
                         }
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

foldAssocMapWithKey :: (a -> k -> b -> a) -> a -> AssocMap.Map k b -> a
foldAssocMapWithKey f acc = foldl' decF acc . AssocMap.toList
  where decF a (k, v) = f a k v

toSymItem :: Ord k => SymVal v => Map k (SBV v) -> k -> v -> Map k (SBV v)
toSymItem acc k v = M.insert k (literal v) acc

toSymMap :: Ord k => SymVal v => AssocMap.Map k v -> Map k (SBV v)
toSymMap = foldAssocMapWithKey toSymItem M.empty

emptySymState :: [(SInteger, SInteger, SInteger, SInteger)] -> Maybe State
              -> Symbolic SymState
emptySymState pt Nothing = do (ls, hs) <- generateSymbolicInterval Nothing
                              return $ SymState { lowSlot = ls
                                                , highSlot = hs
                                                , traces = []
                                                , paramTrace = pt
                                                , symAccounts = M.empty
                                                , symChoices = M.empty
                                                , symBoundValues = M.empty }
emptySymState pt (Just State { accounts = accs
                             , choices = cho
                             , boundValues = bVal
                             , minSlot = ms }) =
  do (ls, hs) <- generateSymbolicInterval (Just (getSlot ms))
     return $ SymState { lowSlot = ls
                       , highSlot = hs
                       , traces = []
                       , paramTrace = pt
                       , symAccounts = toSymMap accs
                       , symChoices = toSymMap cho
                       , symBoundValues = toSymMap bVal }

getSymValFrom :: Maybe SymInput -> SInteger
getSymValFrom Nothing                       = 0
getSymValFrom (Just (SymDeposit _ _ _ val)) = val
getSymValFrom (Just (SymChoice _ val))      = val
getSymValFrom (Just SymNotify)              = 0

convertToSymbolicTrace :: [(SInteger, SInteger, Maybe SymInput, Integer)] ->
                          [(SInteger, SInteger, SInteger, SInteger)] -> SBool
convertToSymbolicTrace [] [] = sTrue
convertToSymbolicTrace [] ((a, b, c, d):t) = (a .== -1) .&& (b .== -1) .&& (c .== -1) .&&
                                             (d .== -1) .&& convertToSymbolicTrace [] t
convertToSymbolicTrace ((lowS, highS, inp, pos):t) ((a, b, c, d):t2) =
  (lowS .== a) .&& (highS .== b) .&& (getSymValFrom inp .== c) .&& (literal pos .== d) .&&
  convertToSymbolicTrace t t2
convertToSymbolicTrace _ _ = error "Provided symbolic trace is not long enough"

symEvalVal :: Value -> SymState -> SInteger
symEvalVal (AvailableMoney accId tok) symState =
  M.findWithDefault (literal 0) (accId, tok) (symAccounts symState)
symEvalVal (Constant inte) symState = literal inte
symEvalVal (NegValue val) symState = - symEvalVal val symState
symEvalVal (AddValue lhs rhs) symState = symEvalVal lhs symState +
                                         symEvalVal rhs symState
symEvalVal (SubValue lhs rhs) symState = symEvalVal lhs symState -
                                         symEvalVal rhs symState
symEvalVal (ChoiceValue choId defVal) symState =
  M.findWithDefault (symEvalVal defVal symState) choId (symChoices symState)
symEvalVal SlotIntervalStart symState = lowSlot symState
symEvalVal SlotIntervalEnd symState = highSlot symState
symEvalVal (UseValue valId) symState =
  M.findWithDefault (literal 0) valId (symBoundValues symState)


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

addTransaction :: Maybe SymInput -> Timeout -> SymState -> Integer
               -> Symbolic (SBool, SymState)
addTransaction symInput slotTim symState@SymState { lowSlot = oldLowSlot
                                                  , highSlot = oldHighSlot
                                                  , traces = oldTraces } pos =
  do let tim = getSlot slotTim
     newLowSlot <- sInteger_
     newHighSlot <- sInteger_
     constrain (newLowSlot .<= newHighSlot)
     let conditions =
           if isNothing symInput
           then ((oldHighSlot .< literal tim) .||
                 ((oldLowSlot .== newLowSlot) .&& (oldHighSlot .== newHighSlot))) .&&
                (newLowSlot .>= literal tim)
           else (oldHighSlot .< literal tim) .&&
                (newHighSlot .< literal tim) .&&
                (newLowSlot .>= oldLowSlot)
     uSymInput <- updateSymInput symInput
                                (symState { lowSlot = newLowSlot
                                          , highSlot = newHighSlot
                                          , traces = (oldLowSlot, oldHighSlot, symInput, pos)
                                                     :oldTraces })
     return (conditions, uSymInput)

isValidAndFailsAux :: Contract -> SymState
                   -> Symbolic SBool
isValidAndFailsAux Close sState =
  return sFalse
isValidAndFailsAux (Pay accId payee token val cont) sState =
  do let concVal = symEvalVal val sState
     let potentialFailedPayTrace =
          convertToSymbolicTrace ((lowSlot sState, highSlot sState, Nothing, 0)
                                  :traces sState) (paramTrace sState)
     let originalMoney = M.findWithDefault 0 (accId, token) (symAccounts sState)
     let remainingMoneyInAccount = originalMoney - concVal
     let newAccs = M.insert (accId, token) (smax (literal 0) remainingMoneyInAccount)
                                                 (symAccounts sState)
     let finalSState = sState { symAccounts =
           case payee of
             (Account destAccId) ->
                M.insert (accId, token)
                         (smin originalMoney (smax (literal 0) concVal)
                            + M.findWithDefault 0 (destAccId, token) newAccs)
                         newAccs
             _ -> newAccs }
     contRes <- isValidAndFailsAux cont finalSState
     return ((((remainingMoneyInAccount .< 0) -- Partial payment
               .|| (concVal .<= 0)) -- Non-positive payment
              .&& potentialFailedPayTrace)
             .|| contRes)
isValidAndFailsAux (If obs cont1 cont2) sState =
  do let obsVal = symEvalObs obs sState
     contVal1 <- isValidAndFailsAux cont1 sState
     contVal2 <- isValidAndFailsAux cont2 sState
     return (ite obsVal contVal1 contVal2)
isValidAndFailsAux (When list timeout cont) sState =
  isValidAndFailsWhen list timeout cont (const sFalse) sState 1
isValidAndFailsAux (Let valId val cont) sState =
  do let concVal = symEvalVal val sState
     let newBVMap = M.insert valId concVal (symBoundValues sState)
     let newSState = sState { symBoundValues = newBVMap }
     isValidAndFailsAux cont newSState

ensureBounds :: SInteger -> [Bound] -> Symbolic ()
ensureBounds cho [] = return ()
ensureBounds cho (Bound lowBnd hiBnd:t) =
  do constrain (cho .>= literal lowBnd)
     constrain (cho .<= literal hiBnd)

generateValueInBounds :: [Bound] -> Symbolic SInteger
generateValueInBounds bnds =
  do bnd <- sInteger_
     ensureBounds bnd bnds
     return bnd

applyInputConditions maybeSymInput timeout sState pos cont =
  do (newCond, newSState) <- addTransaction maybeSymInput timeout sState pos
     newTrace <- isValidAndFailsAux cont newSState
     return ((newCond, newSState), newTrace)

isValidAndFailsWhen :: [Case Contract] -> Timeout -> Contract -> (SymInput -> SBool)
                    -> SymState -> Integer -> Symbolic SBool
isValidAndFailsWhen [] timeout cont previousMatch sState pos =
  do ((cond, newSState), newTrace)
               <- applyInputConditions Nothing timeout sState 0 cont
     return (ite cond newTrace sFalse)
isValidAndFailsWhen (Case (Deposit accId party token val) cont:rest)
                    timeout timCont previousMatch sState pos =
  do let concVal = symEvalVal val sState
     let symInput = SymDeposit accId party token concVal
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymDeposit otherAccId otherParty otherToken otherConcVal ->
               if (otherAccId == accId) && (otherParty == party)
                  && (otherToken == token)
               then (otherConcVal .== concVal) .|| previousMatch otherSymInput
               else previousMatch otherSymInput
             _ -> previousMatch otherSymInput
     ((newCond, newSState), newTrace)
               <- applyInputConditions (Just symInput) timeout sState pos cont
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& newTrace)
                 newTrace
                 ((newCond .&& (concVal .<= 0) -- Non-positive deposit warning
                           .&& convertToSymbolicTrace (traces newSState)
                                                      (paramTrace sState))
                  .|| contTrace))
isValidAndFailsWhen (Case (Choice choId bnds) cont:rest)
                    timeout timCont previousMatch sState pos =
  do concVal <- generateValueInBounds bnds
     let symInput = SymChoice choId concVal
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymChoice otherChoId otherConcVal ->
               if otherChoId == choId
               then (otherConcVal .== concVal) .|| previousMatch otherSymInput
               else previousMatch otherSymInput
             _ -> previousMatch otherSymInput
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     ((newCond, newSState), newTrace)
               <- applyInputConditions (Just symInput) timeout sState pos cont
     return (ite (newCond .&& newTrace) newTrace contTrace)
isValidAndFailsWhen (Case (Notify obs) cont:rest)
                    timeout timCont previousMatch sState pos =
  do let obsRes = symEvalObs obs sState
     let symInput = SymNotify
     let clashResult = previousMatch symInput
     let newPreviousMatch otherSymInput =
           case otherSymInput of
             SymNotify -> sNot obsRes
             _         -> previousMatch otherSymInput
     (newCond, newSState) <- addTransaction (Just symInput) timeout sState pos
     newTrace <- isValidAndFailsAux cont newSState
     contTrace <- isValidAndFailsWhen rest timeout timCont newPreviousMatch sState (pos + 1)
     return (ite (newCond .&& obsRes .&& newTrace) newTrace contTrace)

-- SBV handling and result extraction

countWhens :: Contract -> Integer
countWhens Close               = 0
countWhens (Pay uv uw ux uy c) = countWhens c
countWhens (If uz c c2)        = max (countWhens c) (countWhens c2)
countWhens (When cl t c)       = 1 + max (countWhensCaseList cl) (countWhens c)
countWhens (Let va vb c)       = countWhens c

countWhensCaseList :: [Case Contract] -> Integer
countWhensCaseList (Case uu c : tail) = max (countWhens c) (countWhensCaseList tail)
countWhensCaseList []                 = 0

wrapper :: Contract -> [(SInteger, SInteger, SInteger, SInteger)] -> Maybe State
        -> Symbolic SBool
wrapper c st maybeState = do ess <- emptySymState st maybeState
                             isValidAndFailsAux c ess

generateLabelsAux :: Integer -> Integer -> [String]
generateLabelsAux n m
  | n > m = []
  | otherwise = (action_label ++ "minSlot"):
                (action_label ++ "maxSlot"):
                (action_label ++ "value"):
                (action_label ++ "branch"):
                generateLabelsAux (n + 1) m
     where action_label = "action_" ++ show n ++ "_"

generateLabels :: Integer -> [String]
generateLabels = generateLabelsAux 1

generateParameters :: [String] -> SymbolicT IO [(SInteger, SInteger, SInteger, SInteger)]
generateParameters (sl:sh:v:b:t) =
   do isl <- sInteger sl
      ish <- sInteger sh
      iv <- sInteger v
      ib <- sInteger b
      rest <- generateParameters t
      return ((isl, ish, iv, ib):rest)
generateParameters [] = return []
generateParameters _ = error "Wrong number of labels generated"

groupResult :: [String] -> Map String Integer -> [(Integer, Integer, Integer, Integer)]
groupResult (sl:sh:v:b:t) mappings =
    if ib == -1 then []
    else (isl, ish, iv, ib):groupResult t mappings
  where (Just isl) = M.lookup sl mappings
        (Just ish) = M.lookup sh mappings
        (Just iv) = M.lookup v mappings
        (Just ib) = M.lookup b mappings
groupResult [] _ = []
groupResult _ _ = error "Wrong number of labels generated"

caseToInput :: [Case a] -> Integer -> Integer -> Input
caseToInput [] _ _ = error "Wrong number of cases interpreting result"
caseToInput (Case h _:t) c v
  | c > 1 = caseToInput t (c - 1) v
  | c == 1 = case h of
               Deposit accId party tok _ -> IDeposit accId party tok v
               Choice choId _            -> IChoice choId v
               Notify _                  -> INotify
  | otherwise = error "Negative case number"

computeAndContinue :: ([Input] -> TransactionInput) -> [Input] -> State -> Contract
                   -> [(Integer, Integer, Integer, Integer)]
                   -> [([TransactionInput], [TransactionWarning])]
computeAndContinue transaction inps sta cont t =
  case computeTransaction (transaction inps) sta cont of
    Error TEUselessTransaction -> executeAndInterpret sta t cont
    TransactionOutput { txOutWarnings = war
                      , txOutState = newSta
                      , txOutContract = newCont}
                          -> ([transaction inps], war)
                             :executeAndInterpret newSta t newCont


executeAndInterpret :: State -> [(Integer, Integer, Integer, Integer)] -> Contract
                    -> [([TransactionInput], [TransactionWarning])]
executeAndInterpret sta [] cont = []
executeAndInterpret sta ((l, h, v, b):t) cont
  | b == 0 = computeAndContinue transaction [] sta cont t
  | otherwise =
       case reduceContractUntilQuiescent env sta cont of
         ContractQuiescent _ _ _ tempCont ->
           case tempCont of
             When cases _ _ -> computeAndContinue transaction
                                  [caseToInput cases b v] sta cont t
             _ -> error "Cannot interpret result"
         _ -> error "Error reducing contract when interpreting result"
  where mySlotInterval = (Slot l, Slot h)
        env = Environment { slotInterval = mySlotInterval }
        transaction inputs = TransactionInput { txInterval = mySlotInterval
                                              , txInputs = inputs
                                              }

interpretResult :: [(Integer, Integer, Integer, Integer)] -> Contract -> Maybe State
                -> (Slot, [TransactionInput], [TransactionWarning])
interpretResult [] _ _ = error "Empty result"
interpretResult t@((l, h, v, b):_) c maybeState = (Slot l, tin, twa)
   where (tin, twa) = foldl' (\(accInp, accWarn) (elemInp, elemWarn) ->
                                 (accInp ++ elemInp, accWarn ++ elemWarn)) ([], []) $
                             executeAndInterpret initialState t c
         initialState = case maybeState of
                          Nothing -> emptyState (Slot l)
                          Just x  -> x

extractCounterExample :: SMTModel -> Contract -> Maybe State -> [String]
                      -> (Slot, [TransactionInput], [TransactionWarning])
extractCounterExample smtModel cont maybeState maps = interpretedResult
  where assocs = map (\(a, b) -> (a, fromCV b :: Integer)) $ modelAssocs smtModel
        counterExample = groupResult maps (M.fromList assocs)
        interpretedResult = interpretResult (reverse counterExample) cont maybeState

warningsTraceWithState :: Contract
              -> Maybe State
              -> IO (Either ThmResult
                            (Maybe (Slot, [TransactionInput], [TransactionWarning])))
warningsTraceWithState con maybeState =
    do thmRes@(ThmResult result) <- satCommand
       return (case result of
                 Unsatisfiable _ _ -> Right Nothing
                 Satisfiable _ smtModel ->
                    Right (Just (extractCounterExample smtModel con maybeState params))
                 _ -> Left thmRes)
  where maxActs = 1 + countWhens con
        params = generateLabels maxActs
        property = do v <- generateParameters params
                      r <- wrapper con v maybeState
                      return (sNot r)
        satCommand = proveWith z3 property

warningsTrace :: Contract
              -> IO (Either ThmResult
                            (Maybe (Slot, [TransactionInput], [TransactionWarning])))
warningsTrace con = warningsTraceWithState con Nothing


