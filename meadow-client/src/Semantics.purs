module Semantics where

import Data.BigInt (BigInt, fromInt, toString)
import Data.Eq (class Eq, (/=), (==))
import Data.EuclideanRing (div, mod)
import Data.HeytingAlgebra (not, (&&), (||))
import Data.List (List(..), concat, foldl, foldr)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (class Ord, max, (<), (<=), (>), (>=))
import Data.Ring (negate, (*), (+), (-))
import Data.Show (class Show)
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Prelude (show)

import Data.Foldable as F
import Data.Map as M
import Data.Set as S

type BlockNumber
  = BigInt

type Timeout
  = BlockNumber

type Person
  = BigInt

type Choice
  = BigInt

type IdAction
  = BigInt

type IdCommit
  = BigInt

type IdChoice
  = {choice :: BigInt, person :: Person}

data WIdChoice
  = WIdChoice IdChoice

derive instance eqWIdChoice :: Eq WIdChoice

derive instance ordWIdChoice :: Ord WIdChoice

type IdOracle
  = BigInt

type LetLabel
  = BigInt

showIdChoice :: IdChoice -> String
showIdChoice { choice, person } = joinWith "" [ "("
                                              , toString choice
                                              , ", "
                                              , toString person
                                              , ")"
                                              ]

data Value
  = CurrentBlock
  | Committed IdCommit
  | Constant BigInt
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | DivValue Value Value Value
  | ModValue Value Value Value
  | ValueFromChoice IdChoice Value
  | ValueFromOracle IdOracle Value

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

instance showValue :: Show Value where
  show CurrentBlock = "CurrentBlock"
  show (Committed idCommit) = joinWith "" ["Committed ", toString idCommit]
  show (Constant bigInt) = joinWith "" ["Constant ", toString bigInt]
  show (NegValue value1) = joinWith "" ["NegValue (", show value1, ")"]
  show (AddValue value1 value2) = joinWith "" [ "AddValue ("
                                              , show value1
                                              , ") ("
                                              , show value2
                                              , ")"
                                              ]
  show (SubValue value1 value2) = joinWith "" [ "SubValue ("
                                              , show value1
                                              , ") ("
                                              , show value2
                                              , ")"
                                              ]
  show (MulValue value1 value2) = joinWith "" [ "MulValue ("
                                              , show value1
                                              , ") ("
                                              , show value2
                                              , ")"
                                              ]
  show (DivValue value1 value2 value3) = joinWith "" [ "DivValue ("
                                                     , show value1
                                                     , ") ("
                                                     , show value2
                                                     , ") ("
                                                     , show value3
                                                     , ")"
                                                     ]
  show (ModValue value1 value2 value3) = joinWith "" [ "ModValue ("
                                                     , show value1
                                                     , ") ("
                                                     , show value2
                                                     , ") ("
                                                     , show value3
                                                     , ")"
                                                     ]
  show (ValueFromChoice idChoice value) = joinWith "" [ "ValueFromChoice "
                                                      , showIdChoice idChoice
                                                      , " ("
                                                      , show value
                                                      , ")"
                                                      ]
  show (ValueFromOracle idOracle value) = joinWith "" [ "ValueFromOracle "
                                                      , toString idOracle
                                                      , " ("
                                                      , show value
                                                      , ")"
                                                      ]

data Observation
  = BelowTimeout Timeout
  | AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseThis IdChoice Choice
  | ChoseSomething IdChoice
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

instance showObservation :: Show Observation where
  show (BelowTimeout timeout) = joinWith " " ["BelowTimeout", toString timeout]
  show (AndObs observation1 observation2) = joinWith "" [ "AndObs ("
                                                        , show observation1
                                                        , ") ("
                                                        , show observation2
                                                        , ")"
                                                        ]
  show (OrObs observation1 observation2) = joinWith "" [ "OrObs ("
                                                       , show observation1
                                                       , ") ("
                                                       , show observation2
                                                       , ")"
                                                       ]
  show (NotObs observation) = joinWith "" ["NotObs (", show observation, ")"]
  show (ChoseThis idChoice choice) = joinWith " " [ "ChoseThis"
                                                  , showIdChoice idChoice
                                                  , toString choice
                                                  ]
  show (ChoseSomething idChoice) = joinWith " " [ "ChoseSomething"
                                                , showIdChoice idChoice
                                                ]
  show (ValueGE value1 value2) = joinWith "" [ "ValueGE ("
                                             , show value1
                                             , ") ("
                                             , show value2
                                             , ")"
                                             ]
  show (ValueGT value1 value2) = joinWith "" [ "ValueGT ("
                                             , show value1
                                             , ") ("
                                             , show value2
                                             , ")"
                                             ]
  show (ValueLT value1 value2) = joinWith "" [ "ValueLT ("
                                             , show value1
                                             , ") ("
                                             , show value2
                                             , ")"
                                             ]
  show (ValueLE value1 value2) = joinWith "" [ "ValueLE ("
                                             , show value1
                                             , ") ("
                                             , show value2
                                             , ")"
                                             ]
  show (ValueEQ value1 value2) = joinWith "" [ "ValueEQ ("
                                             , show value1
                                             , ") ("
                                             , show value2
                                             , ")"
                                             ]
  show TrueObs = "TrueObs"
  show FalseObs = "FalseObs"

data Contract
  = Null
  | Commit IdAction IdCommit Person Value Timeout Timeout Contract Contract
  | Pay IdAction IdCommit Person Value Timeout Contract Contract
  | Both Contract Contract
  | Choice Observation Contract Contract
  | When Observation Timeout Contract Contract
  | While Observation Timeout Contract Contract
  | Scale Value Value Value Contract
  | Let LetLabel Contract Contract
  | Use LetLabel

derive instance eqContract :: Eq Contract

derive instance ordContract :: Ord Contract

instance showContract :: Show Contract where
  show Null = "Null"
  show (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) = joinWith "" [ "Commit "
                                                                                                   , toString idAction
                                                                                                   , " "
                                                                                                   , toString idCommit
                                                                                                   , " "
                                                                                                   , toString person
                                                                                                   , " ("
                                                                                                   , show value
                                                                                                   , ") "
                                                                                                   , toString timeout1
                                                                                                   , " "
                                                                                                   , toString timeout2
                                                                                                   , " ("
                                                                                                   , show contract1
                                                                                                   , ") ("
                                                                                                   , show contract2
                                                                                                   , ")"
                                                                                                   ]
  show (Pay idAction idCommit person value timeout contract1 contract2) = joinWith "" [ "Pay "
                                                                                      , toString idAction
                                                                                      , " "
                                                                                      , toString idCommit
                                                                                      , " "
                                                                                      , toString person
                                                                                      , " ("
                                                                                      , show value
                                                                                      , ") "
                                                                                      , toString timeout
                                                                                      , " ("
                                                                                      , show contract1
                                                                                      , ") ("
                                                                                      , show contract2
                                                                                      , ")"
                                                                                      ]
  show (Both contract1 contract2) = joinWith "" [ "Both ("
                                                , show contract1
                                                , ") ("
                                                , show contract2
                                                , ")"
                                                ]
  show (Choice observation contract1 contract2) = joinWith "" [ "Choice ("
                                                              , show observation
                                                              , ") ("
                                                              , show contract1
                                                              , ") ("
                                                              , show contract2
                                                              , ")"
                                                              ]
  show (When observation timeout contract1 contract2) = joinWith "" [ "When ("
                                                                    , show observation
                                                                    , ") "
                                                                    , toString timeout
                                                                    , " ("
                                                                    , show contract1
                                                                    , ") ("
                                                                    , show contract2
                                                                    , ")"
                                                                    ]
  show (While observation timeout contract1 contract2) = joinWith "" [ "While ("
                                                                     , show observation
                                                                     , ") "
                                                                     , toString timeout
                                                                     , " ("
                                                                     , show contract1
                                                                     , ") ("
                                                                     , show contract2
                                                                     , ")"
                                                                     ]
  show (Scale value1 value2 value3 contract) = joinWith "" [ "Scale ("
                                                           , show value1
                                                           , ") ("
                                                           , show value2
                                                           , ") ("
                                                           , show value3
                                                           , ") ("
                                                           , show contract
                                                           , ")"
                                                           ]
  show (Let letLabel contract1 contract2) = joinWith "" [ "Let "
                                                        , toString letLabel
                                                        , " ("
                                                        , show contract1
                                                        , ") ("
                                                        , show contract2
                                                        , ")"
                                                        ]
  show (Use letLabel) = joinWith "" ["Use ", toString letLabel]

-- Data type for Inputs with their information
data Input
  = IChoice IdChoice Choice
  | IOracle IdOracle BlockNumber BigInt

derive instance eqInput :: Eq Input

derive instance ordInput :: Ord Input

data AnyInput
  = Action IdAction
  | Input Input

derive instance eqAnyInput :: Eq AnyInput

derive instance ordAnyInput :: Ord AnyInput

data IdInput
  = IdChoice IdChoice
  | IdOracle IdOracle

derive instance eqIdInput :: Eq IdInput

derive instance ordIdInput :: Ord IdInput

type TimeoutData
  = M.Map Timeout (S.Set IdCommit)

type CommitInfoRecord
  = {person :: Person, amount :: BigInt, timeout :: Timeout}

data CommitInfo
  = CommitInfo {redeemedPerPerson :: M.Map Person BigInt, currentCommitsById :: M.Map IdCommit CommitInfoRecord, expiredCommitIds :: S.Set IdCommit, timeoutData :: TimeoutData}

type OracleDataPoint
  = {blockNumber :: BlockNumber, value :: BigInt}

data State
  = State {commits :: CommitInfo, choices :: M.Map WIdChoice Choice, oracles :: M.Map IdOracle OracleDataPoint, usedIds :: S.Set IdAction}

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
  BigInt ->
  Timeout ->
  State ->
  State
addCommit idCommit person value timeout (State state) = State (state { commits = CommitInfo (ci { currentCommitsById = M.insert idCommit ({ person
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
  Just v -> Just v.person
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
  Just v -> State (state { commits = CommitInfo (ci { currentCommitsById = M.delete idCommit commById, timeoutData = removeFromCommByTim v.timeout idCommit timData }) })
  Nothing -> State state
  where
  CommitInfo ci = state.commits
  commById = ci.currentCommitsById
  timData = ci.timeoutData

-- Get expired not collected for person
getRedeemedForPersonCI ::
  Person ->
  CommitInfo ->
  BigInt
getRedeemedForPersonCI person (CommitInfo ci) = fromMaybe (fromInt 0) (M.lookup person ci.redeemedPerPerson)

getRedeemedForPerson :: Person -> State -> BigInt
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

discountAvailableMoneyFromCommit :: IdCommit -> BigInt -> State -> Maybe State
discountAvailableMoneyFromCommit idCommit discount (State state) = case M.lookup idCommit commById of
  Just { person, amount, timeout } -> Just (State (state { commits = CommitInfo (ci { currentCommitsById = M.insert idCommit ({ person
                                                                                                                              , amount: amount - discount
                                                                                                                              , timeout
                                                                                                                              }) commById }) }))
  Nothing -> Nothing
  where
  CommitInfo ci = state.commits
  commById = ci.currentCommitsById

getAvailableAmountInCommit :: IdCommit -> State -> BigInt
getAvailableAmountInCommit idCommit (State state) = case M.lookup idCommit ci.currentCommitsById of
  Just v -> v.amount
  Nothing -> fromInt 0
  where
  CommitInfo ci = state.commits

-- Collect inputs needed by a contract
collectNeededInputsFromValue ::
  Value ->
  S.Set IdInput
collectNeededInputsFromValue (CurrentBlock) = S.empty

collectNeededInputsFromValue (Committed _) = S.empty

collectNeededInputsFromValue (Constant _) = S.empty

collectNeededInputsFromValue (NegValue value) = collectNeededInputsFromValue value

collectNeededInputsFromValue (AddValue value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                 , collectNeededInputsFromValue value2
                                                                 ]

collectNeededInputsFromValue (SubValue value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                 , collectNeededInputsFromValue value2
                                                                 ]

collectNeededInputsFromValue (MulValue value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                 , collectNeededInputsFromValue value2
                                                                 ]

collectNeededInputsFromValue (DivValue value1 value2 value3) = S.unions [ collectNeededInputsFromValue value1
                                                                        , collectNeededInputsFromValue value2
                                                                        , collectNeededInputsFromValue value3
                                                                        ]

collectNeededInputsFromValue (ModValue value1 value2 value3) = S.unions [ collectNeededInputsFromValue value1
                                                                        , collectNeededInputsFromValue value2
                                                                        , collectNeededInputsFromValue value3
                                                                        ]

collectNeededInputsFromValue (ValueFromChoice idChoice value) = S.unions [ S.singleton (IdChoice idChoice)
                                                                         , collectNeededInputsFromValue value
                                                                         ]

collectNeededInputsFromValue (ValueFromOracle idOracle value) = S.unions [ S.singleton (IdOracle idOracle)
                                                                         , collectNeededInputsFromValue value
                                                                         ]

collectNeededInputsFromObservation :: Observation -> S.Set IdInput
collectNeededInputsFromObservation (BelowTimeout _) = S.empty

collectNeededInputsFromObservation (AndObs observation1 observation2) = S.unions [ collectNeededInputsFromObservation observation1
                                                                                 , collectNeededInputsFromObservation observation2
                                                                                 ]

collectNeededInputsFromObservation (OrObs observation1 observation2) = S.unions [ collectNeededInputsFromObservation observation1
                                                                                , collectNeededInputsFromObservation observation2
                                                                                ]

collectNeededInputsFromObservation (NotObs observation) = collectNeededInputsFromObservation observation

collectNeededInputsFromObservation (ChoseThis idChoice _) = S.singleton (IdChoice idChoice)

collectNeededInputsFromObservation (ChoseSomething idChoice) = S.singleton (IdChoice idChoice)

collectNeededInputsFromObservation (ValueGE value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                      , collectNeededInputsFromValue value2
                                                                      ]

collectNeededInputsFromObservation (ValueGT value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                      , collectNeededInputsFromValue value2
                                                                      ]

collectNeededInputsFromObservation (ValueLT value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                      , collectNeededInputsFromValue value2
                                                                      ]

collectNeededInputsFromObservation (ValueLE value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                      , collectNeededInputsFromValue value2
                                                                      ]

collectNeededInputsFromObservation (ValueEQ value1 value2) = S.unions [ collectNeededInputsFromValue value1
                                                                      , collectNeededInputsFromValue value2
                                                                      ]

collectNeededInputsFromObservation (TrueObs) = S.empty

collectNeededInputsFromObservation (FalseObs) = S.empty

collectNeededInputsFromContract :: Contract -> S.Set IdInput
collectNeededInputsFromContract Null = S.empty

collectNeededInputsFromContract (Commit _ _ _ value _ _ contract1 contract2) = S.unions [ collectNeededInputsFromValue value
                                                                                        , collectNeededInputsFromContract contract1
                                                                                        , collectNeededInputsFromContract contract2
                                                                                        ]

collectNeededInputsFromContract (Pay _ _ _ value _ contract1 contract2) = S.unions [ collectNeededInputsFromValue value
                                                                                   , collectNeededInputsFromContract contract1
                                                                                   , collectNeededInputsFromContract contract2
                                                                                   ]

collectNeededInputsFromContract (Both contract1 contract2) = S.unions [ collectNeededInputsFromContract contract1
                                                                      , collectNeededInputsFromContract contract2
                                                                      ]

collectNeededInputsFromContract (Choice observation contract1 contract2) = S.unions [ collectNeededInputsFromObservation observation
                                                                                    , collectNeededInputsFromContract contract1
                                                                                    , collectNeededInputsFromContract contract2
                                                                                    ]

collectNeededInputsFromContract (When observation _ contract1 contract2) = S.unions [ collectNeededInputsFromObservation observation
                                                                                    , collectNeededInputsFromContract contract1
                                                                                    , collectNeededInputsFromContract contract2
                                                                                    ]

collectNeededInputsFromContract (While observation _ contract1 contract2) = S.unions [ collectNeededInputsFromObservation observation
                                                                                     , collectNeededInputsFromContract contract1
                                                                                     , collectNeededInputsFromContract contract2
                                                                                     ]

collectNeededInputsFromContract (Scale value1 value2 value3 contract) = S.unions [ collectNeededInputsFromValue value1
                                                                                 , collectNeededInputsFromValue value2
                                                                                 , collectNeededInputsFromValue value3
                                                                                 , collectNeededInputsFromContract contract
                                                                                 ]

collectNeededInputsFromContract (Let _ contract1 contract2) = S.unions [ collectNeededInputsFromContract contract1
                                                                       , collectNeededInputsFromContract contract2
                                                                       ]

collectNeededInputsFromContract (Use _) = S.empty

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

addAnyInput _ (Input (IChoice idChoice choice)) neededInputs (State state)
  | (WIdChoice idChoice) `M.member` state.choices = Nothing
  | (IdChoice idChoice) `S.member` neededInputs = Just (State (state { choices = M.insert (WIdChoice idChoice) choice state.choices }))
  | true = Nothing

addAnyInput blockNumber (Input (IOracle idOracle timestamp value)) neededInputs (State state) = case M.lookup idOracle oracleMap of
  Just v -> if (timestamp > v.blockNumber) && (timestamp <= blockNumber) && ((IdOracle idOracle) `S.member` neededInputs)
    then Just newState
    else Nothing
  Nothing -> Just newState
  where
  newState = State (state { oracles = M.insert idOracle { blockNumber: timestamp
                                                        , value
                                                        } oracleMap
                          })
  oracleMap = state.oracles

-- Decides whether something has expired
isExpired ::
  BlockNumber ->
  BlockNumber ->
  Boolean
isExpired currBlockNum expirationBlockNum = currBlockNum >= expirationBlockNum

-- Expire commits
expireOneCommit ::
  IdCommit ->
  CommitInfo ->
  CommitInfo
expireOneCommit idCommit (CommitInfo commitInfo) = CommitInfo case M.lookup idCommit currentCommits of
  Just { person, amount } -> let redeemedBefore = case M.lookup person redPerPer of
                                   Just x -> x
                                   Nothing -> fromInt 0
                             in commitInfo { redeemedPerPerson = M.insert person (redeemedBefore + amount) redPerPer, currentCommitsById = M.delete idCommit currentCommits }
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
  BigInt
evalValue blockNumber _ CurrentBlock = blockNumber

evalValue _ state (Committed idCommit) = getAvailableAmountInCommit idCommit state

evalValue _ _ (Constant value) = value

evalValue blockNumber state (NegValue value) = -(evalValue blockNumber state value)

evalValue blockNumber state (AddValue lhs rhs) = (go lhs) + (go rhs)
  where
  go = evalValue blockNumber state

evalValue blockNumber state (SubValue lhs rhs) = (go lhs) - (go rhs)
  where
  go = evalValue blockNumber state

evalValue blockNumber state (MulValue lhs rhs) = (go lhs) * (go rhs)
  where
  go = evalValue blockNumber state

evalValue blockNumber state (DivValue dividend divisor defaultVal) = if actualDivisor == (fromInt 0)
  then go defaultVal
  else div (go dividend) actualDivisor
  where
  go = evalValue blockNumber state
  actualDivisor = go divisor

evalValue blockNumber state (ModValue dividend divisor defaultVal) = if actualDivisor == (fromInt 0)
  then go defaultVal
  else mod (go dividend) actualDivisor
  where
  go = evalValue blockNumber state
  actualDivisor = go divisor

evalValue blockNumber (State state) (ValueFromChoice idChoice val) = fromMaybe (evalValue blockNumber (State state) val) (M.lookup (WIdChoice idChoice) state.choices)

evalValue blockNumber (State state) (ValueFromOracle idOracle val) = case M.lookup idOracle state.oracles of
  Just v -> v.value
  Nothing -> evalValue blockNumber (State state) val

-- Evaluate an observation
evalObservation ::
  BlockNumber ->
  State ->
  Observation ->
  Boolean
evalObservation blockNumber _ (BelowTimeout timeout) = not (isExpired blockNumber timeout)

evalObservation blockNumber state (AndObs obs1 obs2) = (go obs1) && (go obs2)
  where
  go = evalObservation blockNumber state

evalObservation blockNumber state (OrObs obs1 obs2) = (go obs1) && (go obs2)
  where
  go = evalObservation blockNumber state

evalObservation blockNumber state (NotObs obs) = not (evalObservation blockNumber state obs)

evalObservation _ (State state) (ChoseThis idChoice choice) = case M.lookup (WIdChoice idChoice) (state.choices) of
  Just actualChoice -> actualChoice == choice
  Nothing -> false

evalObservation _ (State state) (ChoseSomething idChoice) = (WIdChoice idChoice) `M.member` (state.choices)

evalObservation blockNumber state (ValueGE val1 val2) = (go val1) >= (go val2)
  where
  go = evalValue blockNumber state

evalObservation blockNumber state (ValueGT val1 val2) = (go val1) > (go val2)
  where
  go = evalValue blockNumber state

evalObservation blockNumber state (ValueLT val1 val2) = (go val1) < (go val2)
  where
  go = evalValue blockNumber state

evalObservation blockNumber state (ValueLE val1 val2) = (go val1) <= (go val2)
  where
  go = evalValue blockNumber state

evalObservation blockNumber state (ValueEQ val1 val2) = (go val1) == (go val2)
  where
  go = evalValue blockNumber state

evalObservation _ _ TrueObs = true

evalObservation _ _ FalseObs = false

isNormalised :: BigInt -> BigInt -> Boolean
isNormalised divid divis = divid == divis && divid /= (fromInt 0)

type Environment
  = M.Map BigInt Contract

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
maxIdFromContract Null = (fromInt 0)

maxIdFromContract (Commit _ _ _ _ _ _ contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (Pay _ _ _ _ _ contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (Both contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (Choice _ contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (When _ _ contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (While _ _ contract1 contract2) = (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (Scale _ _ _ contract) = (maxIdFromContract contract)

maxIdFromContract (Let letLabel contract1 contract2) = max letLabel (max (maxIdFromContract contract1) (maxIdFromContract contract2))

maxIdFromContract (Use letLabel) = letLabel

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

reduceRec blockNum state env c@(When obs timeout cont1 cont2) = if isExpired timeout blockNum
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

reduceRec blockNum state env (While obs timeout contractWhile contractAfter) = if isExpired timeout blockNum
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
simplify_aux ::
  Contract ->
  {contract :: Contract, uses :: S.Set LetLabel}
simplify_aux Null = { contract: Null, uses: S.empty }

simplify_aux (Commit idAction idCommit person value timeout1 timeout2 contract1 contract2) = let v1 = simplify_aux contract1
                                                                                                 v2 = simplify_aux contract2
                                                                                                 contract = Commit idAction idCommit person value timeout1 timeout2 v1.contract v2.contract
                                                                                                 uses = S.union (v1.uses) (v2.uses)
                                                                                             in { contract
                                                                                                , uses
                                                                                                }

simplify_aux (Pay idAction idCommit person value timeout contract1 contract2) = let v1 = simplify_aux contract1
                                                                                    v2 = simplify_aux contract2
                                                                                    contract = Pay idAction idCommit person value timeout v1.contract v2.contract
                                                                                    uses = S.union (v1.uses) (v2.uses)
                                                                                in { contract
                                                                                   , uses
                                                                                   }

simplify_aux (Both contract1 contract2) = case simplify_aux contract1, simplify_aux contract2 of
  v1@{ contract: Null }, v2 -> v2
  v1, v2@{ contract: Null } -> v1
  v1, v2 -> { contract: Both v1.contract v2.contract
            , uses: S.union v1.uses v2.uses
            }

simplify_aux (Choice observation contract1 contract2) = let v1 = simplify_aux contract1
                                                            v2 = simplify_aux contract2
                                                            contract = if (v1.contract == Null) && (v2.contract == Null)
                                                              then Null
                                                              else Choice observation v1.contract v2.contract
                                                            uses = S.union v1.uses v2.uses
                                                        in { contract, uses }

simplify_aux (When observation timeout contract1 contract2) = let v1 = simplify_aux contract1
                                                                  v2 = simplify_aux contract2
                                                                  contract = if (v1.contract == Null) && (v2.contract == Null)
                                                                    then Null
                                                                    else When observation timeout v1.contract v2.contract
                                                                  uses = S.union v1.uses v2.uses
                                                              in { contract
                                                                 , uses
                                                                 }

simplify_aux (While observation timeout contract1 contract2) = let v1 = simplify_aux contract1
                                                                   v2 = simplify_aux contract2
                                                               in if (v1.contract == Null) && (v2.contract == Null)
                                                                 then { contract: Null
                                                                      , uses: S.empty
                                                                      }
                                                                 else { contract: While observation timeout v1.contract v2.contract
                                                                      , uses: S.union v1.uses v2.uses
                                                                      }

simplify_aux (Scale value1 value2 value3 contract) = let v = simplify_aux contract
                                                     in if (v.contract == Null)
                                                       then { contract: Null
                                                            , uses: S.empty
                                                            }
                                                       else { contract: Scale value1 value2 value3 v.contract
                                                            , uses: v.uses
                                                            }

simplify_aux (Let letLabel contract1 contract2) = (let v1 = simplify_aux contract1
                                                       v2 = simplify_aux contract2
                                                   in (if S.member letLabel v2.uses
                                                     then { contract: Let letLabel v1.contract v2.contract
                                                          , uses: S.union v1.uses (S.delete letLabel v2.uses)
                                                          }
                                                     else { contract: v2.contract
                                                          , uses: v2.uses
                                                          }))

simplify_aux (Use letLabel) = { contract: Use letLabel
                              , uses: S.singleton letLabel
                              }

simplify :: Contract -> Contract
simplify c = let v = simplify_aux c
             in v.contract

-- How much everybody pays or receives in transaction
type TransactionOutcomes
  = M.Map Person BigInt

emptyOutcome :: TransactionOutcomes
emptyOutcome = M.empty

isEmptyOutcome :: TransactionOutcomes -> Boolean
isEmptyOutcome trOut = F.all (\x ->
  x == (fromInt 0)) trOut

-- Adds a value to the map of outcomes
addOutcome ::
  Person ->
  BigInt ->
  TransactionOutcomes ->
  TransactionOutcomes
addOutcome person diffValue trOut = M.insert person newValue trOut
  where
  newValue = case M.lookup person trOut of
    Just value -> value + diffValue
    Nothing -> diffValue

-- Get effect of outcomes on the bank of the contract
outcomeEffect ::
  TransactionOutcomes ->
  BigInt
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
  = DCommit IdCommit Person BigInt Timeout
  | DPay IdCommit Person BigInt

derive instance eqDetachedPrimitive :: Eq DetachedPrimitive

derive instance ordDetachedPrimitive :: Ord DetachedPrimitive

-- Semantics of Scale
scaleValue ::
  BigInt ->
  BigInt ->
  BigInt ->
  BigInt ->
  BigInt
scaleValue divid divis def val = if (divis == fromInt 0)
  then def
  else ((val * divid) `div` divis)

scaleResult ::
  BigInt ->
  BigInt ->
  BigInt ->
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
  notCurrentCommit = isCurrentCommit idCommit state
  notExpiredCommit = isExpiredCommit idCommit state
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
areInputPermissionsValid (IChoice cid _) sigs = cid.person `S.member` sigs

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
applyAnyInput anyInput sigs neededInputs blockNum state contract = case addAnyInput blockNum anyInput neededInputs state of
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
redeemMoneyLoop ::
  List Person ->
  TransactionOutcomes ->
  State ->
  {outcome :: TransactionOutcomes, state :: State}
redeemMoneyLoop Nil trOut state = { outcome: trOut, state }

redeemMoneyLoop (Cons h t) trOut state = redeemMoneyLoop t (addOutcome h redeemed trOut) newState
  where
  redeemed = getRedeemedForPerson h state
  newState = resetRedeemedForPerson h state

redeemMoney ::
  S.Set Person ->
  State ->
  {outcome :: TransactionOutcomes, state :: State}
redeemMoney sigs state = redeemMoneyLoop (S.toUnfoldable sigs) emptyOutcome state

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
  BigInt ->
  TransactionOutcomes ->
  List DynamicProblem ->
  MApplicationResult {funds :: BigInt, outcome :: TransactionOutcomes, state :: State, contract :: Contract}
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

applyAnyInputs (Cons h t) sigs neededInputs blockNum state contract value trOut dynProbList = case applyAnyInput h sigs neededInputs blockNum state contract of
  SuccessfullyApplied v newDynProb -> let newValue = value + outcomeEffect v.outcome
                                      in if newValue < fromInt 0
                                        then MCouldNotApply InternalError
                                        else let newTrOut = combineOutcomes v.outcome trOut
                                                 reducedNewContract = reduce blockNum v.state v.contract
                                             in applyAnyInputs t sigs neededInputs blockNum v.state reducedNewContract newValue newTrOut (concat (Cons dynProbList (Cons (Cons newDynProb Nil) Nil)))
  CouldNotApply currError -> MCouldNotApply currError

-- Expire commits and apply applyAnyInputs
applyTransaction ::
  List AnyInput ->
  S.Set Person ->
  BlockNumber ->
  State ->
  Contract ->
  BigInt ->
  MApplicationResult {funds :: BigInt, outcome :: TransactionOutcomes, state :: State, contract :: Contract}
applyTransaction inputs sigs blockNum state contract value = case appResult of
  MSuccessfullyApplied v _ -> if (inputs == Nil) && (reducedContract == contract) && (isEmptyOutcome v.outcome)
    then MCouldNotApply InvalidInput
    else appResult
  _ -> appResult
  where
  neededInputs = collectNeededInputsFromContract contract
  expiredState = expireCommits blockNum state
  reducedContract = reduce blockNum expiredState contract
  appResult = applyAnyInputs inputs sigs neededInputs blockNum expiredState reducedContract value emptyOutcome Nil
