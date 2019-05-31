module Marlowe.Semantics where

import Prelude

import Data.BigInteger (BigInteger, fromInt)
import Data.Foldable (foldMap)
import Data.Foldable as F
import Data.FoldableWithIndex (foldrWithIndexDefault)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.List (List(Nil, Cons), concat, foldl, foldr)
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (mempty)
import Data.Newtype (class Newtype, unwrap, wrap)
import Record (equal)
import Data.Set as S
import Data.Tuple (Tuple(..))
import Marlowe.Types (BlockNumber, Choice, Contract(Use, Let, Scale, While, When, Choice, Both, Pay, Commit, Null), ContractF(..), IdAction, IdChoice, IdCommit, IdOracle, LetLabel, Observation, ObservationF(..), Person, Timeout, Value(..), ValueF(..), WIdChoice(WIdChoice))
import Matryoshka (Algebra, cata)
import Type.Data.Boolean (kind Boolean)

-- Data type for Inputs with their information
data Input
  = IChoice IdChoice Choice
  | IOracle IdOracle BlockNumber BigInteger

derive instance eqInput :: Eq Input

derive instance ordInput :: Ord Input

data AnyInput
  = Action IdAction
  | Input Input

derive instance eqAnyInput :: Eq AnyInput

derive instance ordAnyInput :: Ord AnyInput

data IdInput
  = InputIdChoice IdChoice
  | IdOracle IdOracle

derive instance eqIdInput :: Eq IdInput

derive instance ordIdInput :: Ord IdInput

type TimeoutData
  = M.Map Timeout (S.Set IdCommit)

newtype CommitInfoRecord
  = CommitInfoRecord {person :: Person, amount :: BigInteger, timeout :: Timeout}

derive instance newtypeCommitInfoRecord :: Newtype CommitInfoRecord _
instance eqCommitInfoRecord :: Eq CommitInfoRecord where
  eq = equal `on` unwrap
derive instance genericCommitInfoRecord :: Generic CommitInfoRecord _
instance showCommitInfoRecord :: Show CommitInfoRecord where
  show = genericShow

newtype CommitInfo
  = CommitInfo {redeemedPerPerson :: M.Map Person BigInteger, currentCommitsById :: M.Map IdCommit CommitInfoRecord, expiredCommitIds :: S.Set IdCommit, timeoutData :: TimeoutData}

derive instance newtypeCommitInfo :: Newtype CommitInfo _
instance eqCommitInfo :: Eq CommitInfo where
  eq = equal `on` unwrap
derive instance genericCommitInfo :: Generic CommitInfo _
instance showCommitInfo :: Show CommitInfo where
  show = genericShow

newtype OracleDataPoint
  = OracleDataPoint {blockNumber :: BlockNumber, value :: BigInteger}

derive instance newtypeOracleDataPoint :: Newtype OracleDataPoint _
instance eqOracleDataPoint :: Eq OracleDataPoint where
  eq = equal `on` unwrap
derive instance genericOracleDataPoint :: Generic OracleDataPoint _
instance showOracleDataPoint :: Show OracleDataPoint where
  show = genericShow

newtype State
  = State {commits :: CommitInfo, choices :: M.Map WIdChoice Choice, oracles :: M.Map IdOracle OracleDataPoint, usedIds :: S.Set IdAction}

derive instance newtypeState :: Newtype State _
instance eqState :: Eq State where
  eq = equal `on` unwrap
derive instance genericState :: Generic State _
instance showState :: Show State where
  show = genericShow

emptyCommitInfo :: CommitInfo
emptyCommitInfo = CommitInfo { redeemedPerPerson: M.empty
                             , currentCommitsById: M.empty
                             , expiredCommitIds: S.empty
                             , timeoutData: M.empty
                             }

emptyState :: State
emptyState = State { commits: emptyCommitInfo
                   , choices: M.empty
                   , oracles: M.empty
                   , usedIds: S.empty
                   }

-- Adds a commit identifier to the timeout data map
addToCommByTim ::
  Timeout ->
  IdCommit ->
  TimeoutData ->
  TimeoutData
addToCommByTim timeout idCommit timData = case M.lookup timeout timData of
  Just commSet -> M.insert timeout (S.insert idCommit commSet) timData
  Nothing -> M.insert timeout (S.singleton idCommit) timData

-- Remove a commit identifier from the timeout data map
removeFromCommByTim ::
  Timeout ->
  IdCommit ->
  TimeoutData ->
  TimeoutData
removeFromCommByTim timeout idCommit timData = case M.lookup timeout timData of
  Just commSet -> let newCommSet = S.delete idCommit commSet
                  in if S.isEmpty newCommSet
                    then M.delete timeout timData
                    else M.insert timeout newCommSet timData
  Nothing -> timData

-- Add a commit to CommitInfo
addCommit ::
  IdCommit ->
  Person ->
  BigInteger ->
  Timeout ->
  State ->
  State
addCommit idCommit person value timeout (State state) = State (state { commits = CommitInfo (ci { currentCommitsById = M.insert idCommit (CommitInfoRecord { person
                                                                                                                                          , amount: value
                                                                                                                                          , timeout
                                                                                                                                          }) ci.currentCommitsById, timeoutData = addToCommByTim timeout idCommit ci.timeoutData }) })
  where
  (CommitInfo ci) = state.commits

-- Return the person corresponding to a commit
personForCurrentCommit ::
  IdCommit ->
  State ->
  Maybe Person
personForCurrentCommit idCommit (State state) = case M.lookup idCommit ci.currentCommitsById of
  Just v -> Just (unwrap v).person
  Nothing -> Nothing
  where
  (CommitInfo ci) = state.commits

-- Check whether the commit is current (committed not expired)
isCurrentCommit ::
  IdCommit ->
  State ->
  Boolean
isCurrentCommit idCommit (State { commits: (CommitInfo ci) }) = M.member idCommit ci.currentCommitsById

-- Check whether the commit is expired
isExpiredCommit ::
  IdCommit ->
  State ->
  Boolean
isExpiredCommit idCommit (State state) = idCommit `S.member` ci.expiredCommitIds
  where
  CommitInfo ci = state.commits

-- Remove a current commit from CommitInfo
removeCurrentCommit ::
  IdCommit ->
  State ->
  State
removeCurrentCommit idCommit (State state) = case M.lookup idCommit commById of
  Just v -> State (state { commits = CommitInfo (ci { currentCommitsById = M.delete idCommit commById, timeoutData = removeFromCommByTim (unwrap v).timeout idCommit timData }) })
  Nothing -> State state
  where
  CommitInfo ci = state.commits
  commById = ci.currentCommitsById
  timData = ci.timeoutData

-- Get expired not collected for person
getRedeemedForPersonCI ::
  Person ->
  CommitInfo ->
  BigInteger
getRedeemedForPersonCI person (CommitInfo ci) = fromMaybe (fromInt 0) (M.lookup person ci.redeemedPerPerson)

getRedeemedForPerson :: Person -> State -> BigInteger
getRedeemedForPerson person (State state) = getRedeemedForPersonCI person state.commits

-- Set the amount in redeemedPerPerson to zero
resetRedeemedForPerson ::
  Person ->
  State ->
  State
resetRedeemedForPerson person (State state) = State (state { commits = CommitInfo (ci { redeemedPerPerson = M.delete person rppm }) })
  where
  (CommitInfo ci) = state.commits
  rppm = ci.redeemedPerPerson

discountAvailableMoneyFromCommit ::
  IdCommit ->
  BigInteger ->
  State ->
  Maybe State
discountAvailableMoneyFromCommit idCommit discount (State state) = case M.lookup idCommit commById of
  Just (CommitInfoRecord { person, amount, timeout }) -> Just (State (state { commits = CommitInfo (ci { currentCommitsById = M.insert idCommit (CommitInfoRecord
                                                                                                                              { person
                                                                                                                              , amount: amount - discount
                                                                                                                              , timeout
                                                                                                                              }) commById }) }))
  Nothing -> Nothing
  where
  CommitInfo ci = state.commits
  commById = ci.currentCommitsById

getAvailableAmountInCommit :: IdCommit -> State -> BigInteger
getAvailableAmountInCommit idCommit (State state) = case M.lookup idCommit ci.currentCommitsById of
  Just v -> (unwrap v).amount
  Nothing -> fromInt 0
  where
  CommitInfo ci = state.commits

-- Collect inputs needed by a contract
class InputsFrom a where
  collectNeededInputs :: a -> S.Set IdInput

instance inputsFromValue :: InputsFrom Value where
  collectNeededInputs = cata algebra
    where
      algebra :: Algebra ValueF (S.Set IdInput)
      algebra CurrentBlockF = mempty
      algebra (CommittedF _) = mempty
      algebra (ConstantF _) = mempty
      algebra (NegValueF v) = v
      algebra (AddValueF v1 v2) = v1 <> v2
      algebra (SubValueF v1 v2) = v1 <> v2
      algebra (MulValueF v1 v2) = v1 <> v2
      algebra (DivValueF v1 v2 v3) = v1 <> v2 <> v3
      algebra (ModValueF v1 v2 v3) = v1 <> v2 <> v3
      algebra (ValueFromChoiceF idChoice value) = S.singleton (InputIdChoice idChoice) <> value
      algebra (ValueFromOracleF idOracle value) = S.singleton (IdOracle idOracle) <> value

instance inputsFromObservation :: InputsFrom Observation where
  collectNeededInputs = cata algebra
    where
      algebra :: Algebra ObservationF (S.Set IdInput)
      algebra (BelowTimeoutF _) = mempty
      algebra (AndObsF o1 o2) = o1 <> o2
      algebra (OrObsF o1 o2) = o1 <> o2
      algebra (NotObsF o) = o
      algebra (ChoseThisF idChoice _) = S.singleton (InputIdChoice idChoice)
      algebra (ChoseSomethingF idChoice) = S.singleton (InputIdChoice idChoice)
      algebra (ValueGEF v1 v2) = foldMap collectNeededInputs [v1, v2]
      algebra (ValueGTF v1 v2) = foldMap collectNeededInputs [v1, v2]
      algebra (ValueLTF v1 v2) = foldMap collectNeededInputs [v1, v2]
      algebra (ValueLEF v1 v2) = foldMap collectNeededInputs [v1, v2]
      algebra (ValueEQF v1 v2) = foldMap collectNeededInputs [v1, v2]
      algebra TrueObsF = mempty
      algebra FalseObsF = mempty

instance inputsFromContract :: InputsFrom Contract where
  collectNeededInputs = cata algebra
    where
      algebra :: Algebra ContractF (S.Set IdInput)
      algebra NullF = mempty
      algebra (CommitF _ _ _ value _ _ v1 v2) = collectNeededInputs value <> v1 <> v2
      algebra (PayF _ _ _ value _ v1 v2) = collectNeededInputs value <> v1 <> v2
      algebra (BothF v1 v2) = v1 <> v2
      algebra (ChoiceF o v1 v2) = collectNeededInputs o <> v1 <> v2
      algebra (WhenF o _ v1 v2) = collectNeededInputs o <> v1 <> v2
      algebra (WhileF o _ v1 v2) = collectNeededInputs o <> v1 <> v2
      algebra (ScaleF v1 v2 v3 c) = foldMap collectNeededInputs [v1, v2, v3] <> c
      algebra (LetF _ v1 v2) = v1 <> v2
      algebra (UseF _) = mempty

-- Add inputs and action ids to state.
-- Return Nothing on redundant or irrelevant inputs
addAnyInput ::
  BlockNumber ->
  AnyInput ->
  S.Set IdInput ->
  State ->
  Maybe State
--  current block ---^
addAnyInput _ (Action idInput) _ (State state)
  | idInput `S.member` state.usedIds = Nothing
  | true = Just (State (state { usedIds = S.insert idInput usedIdsSet }))
    where
    usedIdsSet = state.usedIds

addAnyInput _ (Input (IChoice idChoice choice)) collectNeededInputs (State state)
  | (WIdChoice idChoice) `M.member` state.choices = Nothing
  | (InputIdChoice idChoice) `S.member` collectNeededInputs = Just (State (state { choices = M.insert (WIdChoice idChoice) choice state.choices }))
  | true = Nothing

addAnyInput blockNumber (Input (IOracle idOracle timestamp value)) collectNeededInputs (State state) = case M.lookup idOracle oracleMap of
  Just v -> if (timestamp > (unwrap v).blockNumber) && (timestamp <= blockNumber) && ((IdOracle idOracle) `S.member` collectNeededInputs)
    then Just newState
    else Nothing
  Nothing -> Just newState
  where
  newState = State (state { oracles = M.insert idOracle (OracleDataPoint { blockNumber: timestamp
                                                        , value
                                                        }) oracleMap
                          })
  oracleMap = state.oracles

-- Decides whether something has expired
isExpired ::
  BlockNumber ->
  Timeout ->
  Boolean
isExpired currBlockNum timeout = currBlockNum >= unwrap timeout

-- Expire commits
expireOneCommit ::
  IdCommit ->
  CommitInfo ->
  CommitInfo
expireOneCommit idCommit (CommitInfo commitInfo) = CommitInfo case M.lookup idCommit currentCommits of
  Just cir -> let redeemedBefore = case M.lookup (unwrap cir).person redPerPer of
                                   Just x -> x
                                   Nothing -> fromInt 0
                             in commitInfo { redeemedPerPerson = M.insert (unwrap cir).person (redeemedBefore + (unwrap cir).amount) redPerPer, currentCommitsById = M.delete idCommit currentCommits }
  Nothing -> commitInfo
  where
  redPerPer = commitInfo.redeemedPerPerson
  currentCommits = commitInfo.currentCommitsById

expireManyCommits :: S.Set IdCommit -> CommitInfo -> CommitInfo
expireManyCommits commitIds (CommitInfo commitInfo) = foldr expireOneCommit semiUpdatedCI commitIds
  where
  semiUpdatedCI = CommitInfo (commitInfo { expiredCommitIds = S.union expiComms commitIds
                                         })
  expiComms = commitInfo.expiredCommitIds

expireCommitsCI :: BlockNumber -> CommitInfo -> CommitInfo
expireCommitsCI blockNumber (CommitInfo commitInfo) = case M.findMin timData of
  Just res -> let minBlock = res.key
                  commIds = res.value
                  remTimData = M.delete minBlock timData
              in if isExpired blockNumber minBlock
                then let partUpdatedCommitInfo = CommitInfo (commitInfo { timeoutData = remTimData
                                                                        })
                         updatedCommitInfo = expireManyCommits commIds partUpdatedCommitInfo
                     in expireCommitsCI blockNumber updatedCommitInfo
                else CommitInfo commitInfo
  Nothing -> CommitInfo commitInfo
  where
  timData = commitInfo.timeoutData

expireCommits :: BlockNumber -> State -> State
expireCommits blockNumber (State state) = State (state { commits = expireCommitsCI blockNumber commitInfo })
  where
  commitInfo = state.commits

-- Evaluate a value

evalValue ::
  BlockNumber ->
  State ->
  Value ->
  BigInteger
evalValue blockNumber state = cata algebra
  where
    algebra :: Algebra ValueF BigInteger
    algebra CurrentBlockF = wrap $ unwrap blockNumber
    algebra (CommittedF idCommit) = getAvailableAmountInCommit idCommit state
    algebra (ConstantF value) = value
    algebra (NegValueF value) = -value
    algebra (AddValueF v1 v2) = v1 + v2
    algebra (SubValueF v1 v2) = v1 - v2
    algebra (MulValueF v1 v2) = v1 * v2
    algebra (DivValueF dividend divisor defaultValue) = if divisor == fromInt 0 then defaultValue else div dividend divisor
    algebra (ModValueF dividend divisor defaultValue) = if divisor == fromInt 0 then defaultValue else mod dividend divisor
    algebra (ValueFromChoiceF idChoice val) = fromMaybe val $ M.lookup (WIdChoice idChoice) (unwrap state).choices
    algebra (ValueFromOracleF idOracle val) = fromMaybe val <<< map (unwrap >>> _.value) $ M.lookup idOracle (unwrap state).oracles

-- Evaluate an observation


evalObservation ::
  BlockNumber ->
  State ->
  Observation ->
  Boolean
evalObservation blockNumber state = cata algebra
  where
    algebra :: Algebra ObservationF Boolean
    algebra (BelowTimeoutF timeout) = not (isExpired blockNumber timeout)
    algebra (AndObsF o1 o2) = o1 && o2
    algebra (OrObsF o1 o2) = o1 || o2
    algebra (NotObsF o) = not o
    algebra (ChoseThisF idChoice choice) = case M.lookup (WIdChoice idChoice) (unwrap state).choices of
                                            Just actualChoice -> choice == actualChoice
                                            Nothing -> false
    algebra (ChoseSomethingF idChoice) = (WIdChoice idChoice) `M.member` (unwrap state).choices
    algebra (ValueGEF v1 v2) = v1 >= v2
    algebra (ValueGTF v1 v2) = v1 > v2
    algebra (ValueLTF v1 v2) = v1 < v2
    algebra (ValueLEF v1 v2) = v1 <= v2
    algebra (ValueEQF v1 v2) = v1 == v2
    algebra TrueObsF = true
    algebra FalseObsF = false

isNormalised :: BigInteger -> BigInteger -> Boolean
isNormalised divid divis = divid == divis && divid /= (fromInt 0)

type Environment
  = M.Map BigInteger Contract

emptyEnvironment :: Environment
emptyEnvironment = M.empty

addToEnvironment :: LetLabel -> Contract -> Environment -> Environment
addToEnvironment = M.insert

lookupEnvironment :: LetLabel -> Environment -> Maybe Contract
lookupEnvironment = M.lookup

-- Find the highest label in the given Contract (assuming there is an order to LetLabels)
maxIdFromContract ::
  Contract ->
  LetLabel
maxIdFromContract = cata algebra
  where
    algebra :: Algebra ContractF LetLabel
    algebra NullF = fromInt 0
    algebra (CommitF _ _ _ _ _ _ contract1 contract2) = max contract1 contract2
    algebra (PayF _ _ _ _ _ contract1 contract2) = max contract1 contract2
    algebra (BothF contract1 contract2) = max contract1 contract2
    algebra (ChoiceF _ contract1 contract2) = max contract1 contract2
    algebra (WhenF _ _ contract1 contract2) = max contract1 contract2
    algebra (WhileF _ _ contract1 contract2) = max contract1 contract2
    algebra (ScaleF _ _ _ contract) = contract
    algebra (LetF letLabel contract1 contract2) = max letLabel (max contract1 contract2)
    algebra (UseF letLabel) = letLabel

-- Looks for an unused label in the Environment and Contract provided
-- (assuming that labels are numbers)
getFreshLabel ::
  Environment ->
  Contract ->
  LetLabel
getFreshLabel env c = (fromInt 1) + (max (case M.findMax env of
  Nothing -> fromInt 0
  Just v -> v.key) (maxIdFromContract c))

-- We check subcontract in case it uses undefined labels
-- (to prevent potential infinite loop)
-- Optimisation: We do not need to check existing bindings because all
-- contracts are nullified before being added to Environment;
-- Ensures all Use are defined in Environment, if they are not
-- they are replaced with Null
nullifyInvalidUses ::
  Environment ->
  Contract ->
  Contract
nullifyInvalidUses _ Null = Null

nullifyInvalidUses env (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) = Commit idAction idCommit person value timeout1 timeout2 (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (Pay idAction idCommit person value timeout contract1 contract2) = Pay idAction idCommit person value timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (Both contract1 contract2) = Both (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (Choice observation contract1 contract2) = Choice observation (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (When observation timeout contract1 contract2) = When observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (While observation timeout contract1 contract2) = While observation timeout (nullifyInvalidUses env contract1) (nullifyInvalidUses env contract2)

nullifyInvalidUses env (Scale value1 value2 value3 contract) = Scale value1 value2 value3 (nullifyInvalidUses env contract)

nullifyInvalidUses env (Let letLabel contract1 contract2) = Let letLabel (nullifyInvalidUses env contract1) (nullifyInvalidUses newEnv contract2)
  where
  newEnv = addToEnvironment letLabel Null env

-- We just need to mark it as available for this function
nullifyInvalidUses env (Use letLabel) = case lookupEnvironment letLabel env of
  Nothing -> Null
  Just _ -> Use letLabel

-- Replaces a label with another one (unless it is shadowed)
relabel ::
  LetLabel ->
  LetLabel ->
  Contract ->
  Contract
relabel _ _ Null = Null

relabel startLabel endLabel (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) = Commit idAction idCommit person value timeout1 timeout2 (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (Pay idAction idCommit person value timeout contract1 contract2) = Pay idAction idCommit person value timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (Both contract1 contract2) = Both (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (Choice observation contract1 contract2) = Choice observation (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (When observation timeout contract1 contract2) = When observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (While observation timeout contract1 contract2) = While observation timeout (relabel startLabel endLabel contract1) (relabel startLabel endLabel contract2)

relabel startLabel endLabel (Scale value1 value2 value3 contract) = Scale value1 value2 value3 (relabel startLabel endLabel contract)

relabel startLabel endLabel (Let letLabel contract1 contract2) = Let letLabel (relabel startLabel endLabel contract1) (if (letLabel == startLabel)
  then contract2
  else relabel startLabel endLabel contract2)

relabel startLabel endLabel (Use letLabel) = if (letLabel == startLabel)
  then Use endLabel
  else Use letLabel

-- Reduce non actionable primitives and remove expired
reduceRec ::
  BlockNumber ->
  State ->
  Environment ->
  Contract ->
  Contract
reduceRec _ _ _ Null = Null

reduceRec blockNum state env c@(Commit _ _ _ _ timeout_start timeout_end _ continuation) = if (isExpired blockNum timeout_start) || (isExpired blockNum timeout_end)
  then reduceRec blockNum state env continuation
  else c

reduceRec blockNum state env c@(Pay _ _ _ _ timeout _ continuation) = if isExpired blockNum timeout
  then reduceRec blockNum state env continuation
  else c

reduceRec blockNum state env (Both cont1 cont2) = Both (go cont1) (go cont2)
  where
  go = reduceRec blockNum state env

reduceRec blockNum state env (Choice obs cont1 cont2) = reduceRec blockNum state env (if (evalObservation blockNum state obs)
  then cont1
  else cont2)

reduceRec blockNum state env c@(When obs timeout cont1 cont2) = if isExpired blockNum timeout
  then go cont2
  else if evalObservation blockNum state obs
    then go cont1
    else c
  where
  go = reduceRec blockNum state env

reduceRec blockNum state env (Scale divid divis def contract) = Scale (Constant vsDivid) (Constant vsDivis) (Constant vsDef) (go contract)
  where
  go = reduceRec blockNum state env
  vsDivid = evalValue blockNum state divid
  vsDivis = evalValue blockNum state divis
  vsDef = evalValue blockNum state def

reduceRec blockNum state env (While obs timeout contractWhile contractAfter) = if isExpired blockNum timeout 
  then go contractAfter
  else if evalObservation blockNum state obs
    then (While obs timeout (go contractWhile) contractAfter)
    else go contractAfter
  where
  go = reduceRec blockNum state env

reduceRec blockNum state env (Let label boundContract contract) = case lookupEnvironment label env of
  Nothing -> let newEnv = addToEnvironment label checkedBoundContract env
             in Let label checkedBoundContract (reduceRec blockNum state newEnv contract)
  Just _ -> let freshLabel = getFreshLabel env contract
                newEnv = addToEnvironment freshLabel checkedBoundContract env
                fixedContract = relabel label freshLabel contract
            in Let freshLabel checkedBoundContract (reduceRec blockNum state newEnv fixedContract)
  where
  checkedBoundContract = nullifyInvalidUses env boundContract

reduceRec blockNum state env (Use label) = case lookupEnvironment label env of
  Just contract -> reduceRec blockNum state env contract
  Nothing -> Null

-- Optimisation: We do not need to restore environment of the binding because:
--  * We ensure entries are not overwritten in Environment
--  * We check that all entries of Environment had their Use defined when added
reduce ::
  BlockNumber ->
  State ->
  Contract ->
  Contract
reduce blockNum state contract = reduceRec blockNum state emptyEnvironment contract

-- Reduce useless primitives to Null
simplify :: Contract -> Contract
simplify c = (cata algebra c).contract
  where
    algebra :: Algebra ContractF {contract :: Contract, uses :: S.Set LetLabel}
    algebra NullF = { contract: Null, uses: mempty }
    algebra (CommitF idAction idCommit person value timeout1 timeout2 v1 v2) = { contract: Commit idAction idCommit person value timeout1 timeout2 v1.contract v2.contract
                                                                               , uses: v1.uses <> v2.uses
                                                                               }
    algebra (PayF idAction idCommit person value timeout v1 v2) = { contract: Pay idAction idCommit person value timeout v1.contract v2.contract
                                                                                , uses: v1.uses <> v2.uses
                                                                                }
    algebra (BothF { contract: Null, uses: _} v2) = v2
    algebra (BothF v1 { contract: Null, uses: _}) = v1
    algebra (BothF v1 v2) = { contract: Both v1.contract v2.contract, uses: v1.uses <> v2.uses }
    algebra (ChoiceF observation v1 v2) = let contract = if (v1.contract == Null) && (v2.contract == Null)
                                                then Null
                                                else Choice observation v1.contract v2.contract
                                              uses = v1.uses <> v2.uses
                                          in { contract, uses }
    algebra (WhenF observation timeout v1 v2) = let contract = if (v1.contract == Null) && (v2.contract == Null)
                                                      then Null
                                                      else When observation timeout v1.contract v2.contract
                                                    uses = v1.uses <> v2.uses
                                                in { contract
                                                   , uses
                                                   }
    algebra (WhileF observation timeout v1 v2) = if (v1.contract == Null) && (v2.contract == Null)
                                                 then { contract: Null
                                                      , uses: mempty
                                                      }
                                                 else { contract: While observation timeout v1.contract v2.contract
                                                      , uses: v1.uses <> v2.uses
                                                      }

    algebra (ScaleF value1 value2 value3 v) = if (v.contract == Null)
                                              then { contract: Null
                                                   , uses: mempty
                                                   }
                                              else { contract: Scale value1 value2 value3 v.contract
                                                   , uses: v.uses
                                                   }
    algebra (LetF letLabel v1 v2) = if S.member letLabel v2.uses
                                    then { contract: Let letLabel v1.contract v2.contract
                                         , uses: v1.uses <> (S.delete letLabel v2.uses)
                                         }
                                    else { contract: v2.contract
                                         , uses: v2.uses
                                         }

    algebra (UseF letLabel) = { contract: Use letLabel
                              , uses: S.singleton letLabel
                              }

-- How much everybody pays or receives in transaction
type TransactionOutcomes
  = M.Map Person BigInteger

emptyOutcome :: TransactionOutcomes
emptyOutcome = M.empty

isEmptyOutcome :: TransactionOutcomes -> Boolean
isEmptyOutcome trOut = F.all (\x ->
  x == (fromInt 0)) trOut

-- Adds a value to the map of outcomes
addOutcome ::
  Person ->
  BigInteger ->
  TransactionOutcomes ->
  TransactionOutcomes
addOutcome person diffValue trOut = M.alter f person trOut
  where
    f (Just value) = Just $ value + diffValue
    f Nothing = Just diffValue

-- Get effect of outcomes on the bank of the contract
outcomeEffect ::
  TransactionOutcomes ->
  BigInteger
outcomeEffect trOut = foldl (-) (fromInt 0) trOut

-- Add two transaction outcomes together
combineOutcomes ::
  TransactionOutcomes ->
  TransactionOutcomes ->
  TransactionOutcomes
combineOutcomes = M.unionWith (+)

data FetchResult a
  = Picked a
  | NoMatch
  | MultipleMatches

data DetachedPrimitive
  = DCommit IdCommit Person BigInteger Timeout
  | DPay IdCommit Person BigInteger

derive instance eqDetachedPrimitive :: Eq DetachedPrimitive

derive instance ordDetachedPrimitive :: Ord DetachedPrimitive

-- Semantics of Scale
scaleValue ::
  BigInteger ->
  BigInteger ->
  BigInteger ->
  BigInteger ->
  BigInteger
scaleValue divid divis def val = if (divis == fromInt 0)
  then def
  else ((val * divid) `div` divis)

scaleResult ::
  BigInteger ->
  BigInteger ->
  BigInteger ->
  DetachedPrimitive ->
  DetachedPrimitive
scaleResult divid divis def (DCommit idCommit person val tim) = DCommit idCommit person (scaleValue divid divis def val) tim

scaleResult divid divis def (DPay idCommit person val) = DPay idCommit person (scaleValue divid divis def val)

-- Find out whether the Action is allowed given the current state
-- and contract, and, if so, pick the corresponding primitive in the contract.
-- Also return the contract without the selected primitive.
fetchPrimitive ::
  IdAction ->
  BlockNumber ->
  State ->
  Contract ->
  FetchResult {prim :: DetachedPrimitive, contract :: Contract}
--                                 Remaining contract --^
fetchPrimitive idAction blockNum state (Commit idActionC idCommit person value _ timeout continuation _) = if (idAction == idActionC && notCurrentCommit && notExpiredCommit)
  then Picked { prim: (DCommit idCommit person actualValue timeout)
              , contract: continuation
              }
  else NoMatch
  where
  notCurrentCommit = not (isCurrentCommit idCommit state)
  notExpiredCommit = not (isExpiredCommit idCommit state)
  actualValue = evalValue blockNum state value

fetchPrimitive idAction blockNum state (Pay idActionC idCommit person value _ continuation _) = if (idAction == idActionC)
  then Picked { prim: (DPay idCommit person actualValue)
              , contract: continuation
              }
  else NoMatch
  where
  actualValue = evalValue blockNum state value

fetchPrimitive idAction blockNum state (Both leftContract rightContract) = case Tuple (go leftContract) (go rightContract) of
  Tuple (Picked v) NoMatch -> Picked { prim: v.prim
                                     , contract: Both v.contract rightContract
                                     }
  Tuple NoMatch (Picked v) -> Picked { prim: v.prim
                                     , contract: Both leftContract v.contract
                                     }
  Tuple NoMatch NoMatch -> NoMatch
  _ -> MultipleMatches
  where
  go = fetchPrimitive idAction blockNum state

fetchPrimitive idAction blockNum state (While obs timeout contract1 contract2) = case fetchPrimitive idAction blockNum state contract1 of
  Picked v -> Picked { prim: v.prim
                     , contract: While obs timeout v.contract contract2
                     }
  NoMatch -> NoMatch
  MultipleMatches -> MultipleMatches

fetchPrimitive idAction blockNum state (Let label boundContract subContract) = case fetchPrimitive idAction blockNum state subContract of
  Picked v -> Picked { prim: v.prim
                     , contract: Let label boundContract v.contract
                     }
  NoMatch -> NoMatch
  MultipleMatches -> MultipleMatches

fetchPrimitive idAction blockNum state (Scale divid divis def subContract) = case fetchPrimitive idAction blockNum state subContract of
  Picked v -> Picked { prim: scaleResult sDivid sDivis sDef v.prim
                     , contract: Scale divid divis def v.contract
                     }
  NoMatch -> NoMatch
  MultipleMatches -> MultipleMatches
  where
  sDivid = evalValue blockNum state divid
  sDivis = evalValue blockNum state divis
  sDef = evalValue blockNum state def

fetchPrimitive _ _ _ _ = NoMatch

-- Gather all the primitives that are reachable given the current state of the contract 
scoutPrimitivesAux :: BlockNumber -> State -> Contract -> M.Map IdAction (Maybe DetachedPrimitive)
scoutPrimitivesAux blockNum state (Commit idActionC idCommit person value _ timeout continuation _) =
  if (notCurrentCommit && notExpiredCommit)
  then M.insert idActionC (Just (DCommit idCommit person actualValue timeout)) M.empty
  else M.empty 
  where
  notCurrentCommit = not (isCurrentCommit idCommit state)
  notExpiredCommit = not (isExpiredCommit idCommit state)
  actualValue = evalValue blockNum state value

scoutPrimitivesAux blockNum state (Pay idActionC idCommit person value _ continuation _) =
  M.insert idActionC (Just (DPay idCommit person actualValue)) M.empty
  where
  actualValue = evalValue blockNum state value

scoutPrimitivesAux blockNum state (Both leftContract rightContract) =
  M.unionWith (\_ _ -> Nothing) leftC rightC 
  where
  leftC = go leftContract
  rightC = go rightContract
  go = scoutPrimitivesAux blockNum state

scoutPrimitivesAux blockNum state (While obs timeout contract1 contract2) =
  scoutPrimitivesAux blockNum state contract1

scoutPrimitivesAux blockNum state (Let label boundContract subContract) =
  scoutPrimitivesAux blockNum state subContract

scoutPrimitivesAux blockNum state (Scale divid divis def subContract) =
  map (\x -> (scaleResult sDivid sDivis sDef) <$> x) subC
  where
  subC = scoutPrimitivesAux blockNum state subContract
  sDivid = evalValue blockNum state divid
  sDivis = evalValue blockNum state divis
  sDef = evalValue blockNum state def

scoutPrimitivesAux _ _ _ = M.empty 

data DetachedPrimitiveWIA =
    DWAICommit IdAction IdCommit BigInteger Timeout
  | DWAIPay IdAction IdCommit BigInteger

addMaybePrimitive :: IdAction -> Maybe DetachedPrimitive -> M.Map Person (List DetachedPrimitiveWIA) -> M.Map Person (List DetachedPrimitiveWIA)
addMaybePrimitive _ Nothing x = x
addMaybePrimitive idAction (Just (DCommit idCommit person val timeout)) pmap =
    M.insert person (Cons (DWAICommit idAction idCommit val timeout) plist) pmap
  where
  plist = case M.lookup person pmap of
            Just l -> l
            Nothing -> Nil
addMaybePrimitive idAction (Just (DPay idCommit person val)) pmap =
    M.insert person (Cons (DWAIPay idAction idCommit val) plist) pmap
  where
  plist = case M.lookup person pmap of
            Just l -> l
            Nothing -> Nil

scoutPrimitives :: BlockNumber -> State -> Contract -> M.Map Person (List DetachedPrimitiveWIA)
scoutPrimitives blockNum state contract =
  foldrWithIndexDefault addMaybePrimitive M.empty res
  where res = scoutPrimitivesAux blockNum state contract

data DynamicProblem
  = NoProblem
  | CommitNotMade
  | NotEnoughMoneyLeftInCommit
  | CommitIsExpired

derive instance eqDynamicProblem :: Eq DynamicProblem

derive instance ordDynamicProblem :: Ord DynamicProblem

data EvaluationResult a
  = Result a DynamicProblem
  | InconsistentState

-- This should not happen when using fetchPrimitive result
-- Evaluation of actionable input
eval ::
  DetachedPrimitive ->
  State ->
  EvaluationResult {outcome :: TransactionOutcomes, state :: State}
eval (DCommit idCommit person value timeout) state = if (isCurrentCommit idCommit state) || (isExpiredCommit idCommit state)
  then InconsistentState
  else Result { outcome: addOutcome person (-value) emptyOutcome
              , state: addCommit idCommit person value timeout state
              } NoProblem

eval (DPay idCommit person value) state = if (not (isCurrentCommit idCommit state))
  then (if (not (isExpiredCommit idCommit state))
    then Result { outcome: emptyOutcome, state } CommitNotMade
    else Result { outcome: emptyOutcome, state } CommitIsExpired)
  else (if value > maxValue
    then case discountAvailableMoneyFromCommit idCommit maxValue state of
      Just newState -> Result { outcome: addOutcome person maxValue emptyOutcome
                              , state: newState
                              } NotEnoughMoneyLeftInCommit
      Nothing -> InconsistentState
    else case discountAvailableMoneyFromCommit idCommit value state of
      Just newState -> Result { outcome: addOutcome person value emptyOutcome
                              , state: newState
                              } NoProblem
      Nothing -> InconsistentState)
  where
  maxValue = getAvailableAmountInCommit idCommit state

-- Check whether the person who must sign has signed
areActionPermissionsValid ::
  DetachedPrimitive ->
  S.Set Person ->
  Boolean
areActionPermissionsValid (DCommit _ person _ _) sigs = person `S.member` sigs

areActionPermissionsValid (DPay _ person _) sigs = person `S.member` sigs

areInputPermissionsValid :: Input -> S.Set Person -> Boolean
areInputPermissionsValid (IChoice cid _) sigs = (unwrap cid).person `S.member` sigs

areInputPermissionsValid (IOracle _ _ _) _ = true

-- Implementation ToDo: need to check signature
-- Check whether a commit or payment has negative value
isTransactionNegative ::
  DetachedPrimitive ->
  Boolean
isTransactionNegative (DCommit _ _ val _) = val < (fromInt 0)

isTransactionNegative (DPay _ _ val) = val < (fromInt 0)

data ErrorResult
  = InvalidInput
  | NoValidSignature
  | NegativeTransaction
  | AmbiguousId
  | InternalError

derive instance eqErrorResult :: Eq ErrorResult

derive instance ordErrorResult :: Ord ErrorResult
derive instance genericErrorResult :: Generic ErrorResult _
instance showErrorResult :: Show ErrorResult where
  show = genericShow

data ApplicationResult a
  = SuccessfullyApplied a DynamicProblem
  | CouldNotApply ErrorResult

-- High level wrapper that calls the appropriate update function on contract and state.
-- Does not take care of reducing, that must be done before and after applyAnyInput.
applyAnyInput ::
  AnyInput ->
  S.Set Person ->
  S.Set IdInput ->
  BlockNumber ->
  State ->
  Contract ->
  ApplicationResult {outcome :: TransactionOutcomes, state :: State, contract :: Contract}
applyAnyInput anyInput sigs collectNeededInputs blockNum state contract = case addAnyInput blockNum anyInput collectNeededInputs state of
  Just updatedState -> case anyInput of
    Input input -> if areInputPermissionsValid input sigs
      then SuccessfullyApplied { outcome: emptyOutcome
                               , state: updatedState
                               , contract
                               } NoProblem
      else CouldNotApply NoValidSignature
    Action idAction -> case fetchPrimitive idAction blockNum updatedState contract of
      Picked v -> case eval v.prim updatedState of
        Result v2 dynamicProblem -> if isTransactionNegative v.prim
          then CouldNotApply NegativeTransaction
          else if areActionPermissionsValid v.prim sigs
            then SuccessfullyApplied { outcome: v2.outcome
                                     , state: v2.state
                                     , contract: v.contract
                                     } dynamicProblem
            else CouldNotApply NoValidSignature
        InconsistentState -> CouldNotApply InternalError
      NoMatch -> CouldNotApply InvalidInput
      MultipleMatches -> CouldNotApply AmbiguousId
  Nothing -> CouldNotApply InvalidInput

-- Give redeemed money to owners
redeemMoney ::
  S.Set Person ->
  State ->
  {outcome :: TransactionOutcomes, state :: State}
redeemMoney sigs initialState = foldr f init sigs
  where
    init = {outcome: emptyOutcome, state: initialState} 
    f person c = let
                    redeemed = getRedeemedForPerson person c.state
                  in
                    { outcome: addOutcome person redeemed c.outcome
                    , state: resetRedeemedForPerson person c.state
                    }


data MApplicationResult a
  = MSuccessfullyApplied a (List DynamicProblem)
  | MCouldNotApply ErrorResult

-- Fold applyAnyInput through a list of AnyInputs.
-- Check that balance is positive at every step
-- In the last step: simplify
applyAnyInputs ::
  List AnyInput ->
  S.Set Person ->
  S.Set IdInput ->
  BlockNumber ->
  State ->
  Contract ->
  BigInteger ->
  TransactionOutcomes ->
  List DynamicProblem ->
  MApplicationResult {funds :: BigInteger, outcome :: TransactionOutcomes, state :: State, contract :: Contract}
applyAnyInputs Nil sigs _ _ state contract value trOut dynProbList = let v = redeemMoney sigs state
                                                                         newValue = value + outcomeEffect v.outcome
                                                                     in if newValue < fromInt 0
                                                                       then MCouldNotApply InternalError
                                                                       else let newTrOut = combineOutcomes v.outcome trOut
                                                                                simplifiedContract = simplify contract
                                                                            in MSuccessfullyApplied { funds: newValue
                                                                                                    , outcome: newTrOut
                                                                                                    , state: v.state
                                                                                                    , contract: simplifiedContract
                                                                                                    } dynProbList

applyAnyInputs (Cons h t) sigs collectNeededInputs blockNum state contract value trOut dynProbList = case applyAnyInput h sigs collectNeededInputs blockNum state contract of
  SuccessfullyApplied v newDynProb -> let newValue = value + outcomeEffect v.outcome
                                      in if newValue < fromInt 0
                                        then MCouldNotApply InternalError
                                        else let newTrOut = combineOutcomes v.outcome trOut
                                                 reducedNewContract = reduce blockNum v.state v.contract
                                             in applyAnyInputs t sigs collectNeededInputs blockNum v.state reducedNewContract newValue newTrOut (concat (Cons dynProbList (Cons (Cons newDynProb Nil) Nil)))
  CouldNotApply currError -> MCouldNotApply currError

-- Expire commits and apply applyAnyInputs
applyTransaction ::
  List AnyInput ->
  S.Set Person ->
  BlockNumber ->
  State ->
  Contract ->
  BigInteger ->
  MApplicationResult {funds :: BigInteger, outcome :: TransactionOutcomes, state :: State, contract :: Contract}
applyTransaction inputs sigs blockNum state contract value = case appResult of
  MSuccessfullyApplied v _ -> if (inputs == Nil) && (reducedContract == contract) && (isEmptyOutcome v.outcome)
    then MCouldNotApply InvalidInput
    else appResult
  _ -> appResult
  where
  expiredState = expireCommits blockNum state
  reducedContract = reduce blockNum expiredState contract
  appResult = applyAnyInputs inputs sigs (collectNeededInputs contract) blockNum expiredState reducedContract value emptyOutcome Nil

-- Extract participants from state and contract
class PeopleFrom a where
  peopleFrom :: a -> S.Set Person

instance peopleFromCommitInfo :: PeopleFrom CommitInfo where
  peopleFrom (CommitInfo { redeemedPerPerson: rpp, currentCommitsById: ccbi })
    = S.fromFoldable (M.keys rpp) <> foldMap (unwrap >>> _.person >>> S.singleton) (M.values ccbi)

instance peopleFromState :: PeopleFrom State where
  peopleFrom (State { commits: comm }) = peopleFrom comm

instance peopleFromValue :: PeopleFrom Value where
  peopleFrom = cata algebra
    where
      algebra :: Algebra ValueF (S.Set Person)
      algebra CurrentBlockF = mempty
      algebra (CommittedF _) = mempty
      algebra (ConstantF _) = mempty
      algebra (NegValueF value) = value
      algebra (AddValueF value1 value2) = value1 <> value2
      algebra (SubValueF value1 value2) = value1 <> value2
      algebra (MulValueF value1 value2) = value1 <> value2
      algebra (DivValueF value1 value2 value3) = value1 <> value2 <> value3
      algebra (ModValueF value1 value2 value3) = value1 <> value2 <> value3
      algebra (ValueFromChoiceF v value) = S.singleton (unwrap v).person <> value
      algebra (ValueFromOracleF _ value) = value

instance peopleFromObservation :: PeopleFrom Observation where
  peopleFrom = cata algebra
    where
      algebra :: Algebra ObservationF (S.Set Person)
      algebra (BelowTimeoutF _) = mempty
      algebra (AndObsF observation1 observation2) = observation1 <> observation2
      algebra (OrObsF observation1 observation2) = observation1 <> observation2
      algebra (NotObsF observation) = observation
      algebra (ChoseThisF v _) = S.singleton (unwrap v).person
      algebra (ChoseSomethingF v) = S.singleton (unwrap v).person
      algebra (ValueGEF value1 value2) = peopleFrom value1 <> peopleFrom value2
      algebra (ValueGTF value1 value2) = peopleFrom value1 <> peopleFrom value2
      algebra (ValueLTF value1 value2) = peopleFrom value1 <> peopleFrom value2
      algebra (ValueLEF value1 value2) = peopleFrom value1 <> peopleFrom value2
      algebra (ValueEQF value1 value2) = peopleFrom value1 <> peopleFrom value2
      algebra TrueObsF = mempty
      algebra FalseObsF = mempty

instance peopleFromContract :: PeopleFrom Contract where
  peopleFrom = cata algebra
    where
      algebra :: Algebra ContractF (S.Set Person)
      algebra NullF = mempty
      algebra (CommitF _ _ person value _ _ v1 v2) = S.singleton person <> peopleFrom value <> v1 <> v2
      algebra (PayF _ _ person value _  v1 v2) = S.singleton person <> peopleFrom value <> v1 <> v2
      algebra (BothF v1 v2) = v1 <> v2
      algebra (ChoiceF observation v1 v2) = peopleFrom observation <> v1 <> v2
      algebra (WhenF observation _ v1 v2) = peopleFrom observation <> v1 <> v2
      algebra (WhileF observation _ v1 v2) = peopleFrom observation <> v1 <> v2
      algebra (ScaleF v1 v2 v3 c) = foldMap peopleFrom [v1, v2, v3] <> c
      algebra (LetF _ v1 v2) = v1 <> v2
      algebra (UseF _) = mempty

peopleFromStateAndContract :: State -> Contract -> List Person
peopleFromStateAndContract sta con = S.toUnfoldable (peopleFrom sta <> peopleFrom con)