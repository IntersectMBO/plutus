module Marlowe.Linter
  ( lint
  , State(..)
  , MaxTimeout
  , Warning(..)
  , WarningDetail(..)
  , _holes
  , hasHoles
  , _warnings
  , _metadataHints
  , _location
  ) where

import Prelude
import Control.Monad.State as CMS
import Data.Bifunctor (bimap)
import Data.BigInteger (BigInteger)
import Data.Foldable (foldM)
import Data.FoldableWithIndex (traverseWithIndex_)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', modifying, over, set, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Newtype (class Newtype)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Extended as EM
import Marlowe.Extended.Metadata (MetadataHintInfo, _choiceNames, _roles, _slotParameters, _valueParameters)
import Marlowe.Holes (Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Holes, Location(..), Observation(..), Party(..), Payee(..), Term(..), TermWrapper(..), Value(..), compareLocation, fromTerm, getHoles, getLocation, insertHole)
import Marlowe.Holes as Holes
import Marlowe.Semantics (Rational(..), Slot(..), emptyState, evalValue, makeEnvironment)
import Marlowe.Semantics as S
import Monaco (TextEdit)
import Pretty (showPrettyMoney, showPrettyParty, showPrettyToken)
import StaticAnalysis.Reachability (initializePrefixMap, stepPrefixMap)
import StaticAnalysis.Types (ContractPath, ContractPathStep(..), PrefixMap)
import Text.Pretty (hasArgs, pretty)

newtype MaxTimeout
  = MaxTimeout Slot

derive instance newtypeMaxTimeout :: Newtype MaxTimeout _

derive newtype instance eqMaxTimeout :: Eq MaxTimeout

derive newtype instance ordMaxTimeout :: Ord MaxTimeout

instance semigroupMax :: Semigroup MaxTimeout where
  append a b = max a b

instance monoidMaxTimeout :: Monoid MaxTimeout where
  mempty = MaxTimeout zero

-- We could eventually see if we can make Warning polymorphic on the location, even if Term cannot be.
-- for the moment we don't have static guarantees on the Location type, but runtype exceptions if it
-- is missused.
newtype Warning
  = Warning
  { warning :: WarningDetail
  , location :: Location
  -- FIXME: The Maybe TextEdit only makes sense for LinterText
  , refactoring :: Maybe TextEdit
  }

derive instance newtypeWarning :: Newtype Warning _

_location :: Lens' Warning Location
_location = _Newtype <<< prop (SProxy :: SProxy "location")

data WarningDetail
  = NegativePayment
  | NegativeDeposit
  | TimeoutNotIncreasing
  | UnreachableCaseEmptyChoice
  | InvalidBound
  | UnreachableCaseFalseNotify
  | UnreachableContract
  | UndefinedChoice
  | UndefinedUse
  | ShadowedLet
  | DivisionByZero
  | SimplifiableValue (Term Value) (Term Value)
  | SimplifiableObservation (Term Observation) (Term Observation)
  | PayBeforeDeposit S.AccountId
  | PartialPayment S.AccountId S.Token BigInteger BigInteger

instance showWarningDetail :: Show WarningDetail where
  show NegativePayment = "The contract can make a non-positive payment"
  show NegativeDeposit = "The contract can make a non-positive deposit"
  show TimeoutNotIncreasing = "Timeouts should always increase in value"
  show UnreachableCaseEmptyChoice = "This case will never be used, because there are no options to choose from"
  show InvalidBound = "This pair of bounds is invalid, since the lower bound is greater than the higher bound"
  show UnreachableCaseFalseNotify = "This case will never be used, because the Observation is always false"
  show UnreachableContract = "This contract is unreachable"
  show UndefinedChoice = "The contract uses a ChoiceId that has not been input by a When, so (Constant 0) will be used"
  show UndefinedUse = "The contract uses a ValueId that has not been defined in a Let, so (Constant 0) will be used"
  show ShadowedLet = "Let is redefining a ValueId that already exists"
  show DivisionByZero = "Scale construct divides by zero"
  show (SimplifiableValue oriVal newVal) = "The value \"" <> (show oriVal) <> "\" can be simplified to \"" <> (show newVal) <> "\""
  show (SimplifiableObservation oriVal newVal) = "The observation \"" <> (show oriVal) <> "\" can be simplified to \"" <> (show newVal) <> "\""
  show (PayBeforeDeposit account) = "The contract makes a payment from account " <> showPrettyParty account <> " before a deposit has been made"
  show (PartialPayment accountId tokenId availableAmount demandedAmount) =
    "The contract makes a payment of " <> showPrettyMoney demandedAmount <> " "
      <> showPrettyToken tokenId
      <> " from account "
      <> showPrettyParty accountId
      <> " but the account only has "
      <> showPrettyMoney availableAmount

derive instance genericWarningDetail :: Generic WarningDetail _

instance eqWarningDetail :: Eq WarningDetail where
  eq = genericEq

-- FIXME: This generic Ord requires a lot of instances defined in Marlowe.Holes and only for the fallback
--        case in the ordWarning. I'm not sure if having a generic compare is worth, or we should have a
--        manual definition that indicates which type of warning is "more severe"
instance ordWarningDetail :: Ord WarningDetail where
  compare = genericCompare

derive instance genericWarning :: Generic Warning _

instance eqWarning :: Eq Warning where
  eq = genericEq

-- We order Warnings by their Range first
instance ordWarning :: Ord Warning where
  compare a@(Warning { location: locA }) b@(Warning { location: locB }) =
    let
      locCMP = compareLocation locA locB
    in
      case locCMP of
        EQ -> genericCompare a b
        _ -> locCMP

instance showWarning :: Show Warning where
  show (Warning warn) = show warn.warning

newtype State
  = State
  { holes :: Holes
  , warnings :: Set Warning
  , metadataHints :: MetadataHintInfo
  }

derive instance newtypeState :: Newtype State _

derive newtype instance semigroupState :: Semigroup State

derive newtype instance monoidState :: Monoid State

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_warnings :: Lens' State (Set Warning)
_warnings = _Newtype <<< prop (SProxy :: SProxy "warnings")

_metadataHints :: Lens' State MetadataHintInfo
_metadataHints = _Newtype <<< prop (SProxy :: SProxy "metadataHints")

hasHoles :: State -> Boolean
hasHoles = not Holes.isEmpty <<< view _holes

addRoleFromPartyTerm :: Term Party -> CMS.State State Unit
addRoleFromPartyTerm (Term (Role role) _) = modifying (_metadataHints <<< _roles) $ Set.insert role

addRoleFromPartyTerm _ = pure unit

addSlotParameter :: String -> CMS.State State Unit
addSlotParameter slotParam = modifying (_metadataHints <<< _slotParameters) $ Set.insert slotParam

addValueParameter :: String -> CMS.State State Unit
addValueParameter valueParam = modifying (_metadataHints <<< _valueParameters) $ Set.insert valueParam

addChoiceName :: String -> CMS.State State Unit
addChoiceName choiceName = modifying (_metadataHints <<< _choiceNames) $ Set.insert choiceName

newtype LintEnv
  = LintEnv
  { choicesMade :: Set S.ChoiceId
  , deposits :: Map (S.AccountId /\ S.Token) (Maybe BigInteger)
  , letBindings :: Set S.ValueId
  , maxTimeout :: MaxTimeout
  , isReachable :: Boolean
  , unreachablePaths :: Maybe PrefixMap
  }

derive instance newtypeLintEnv :: Newtype LintEnv _

_choicesMade :: Lens' LintEnv (Set S.ChoiceId)
_choicesMade = _Newtype <<< prop (SProxy :: SProxy "choicesMade")

_letBindings :: Lens' LintEnv (Set S.ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

_maxTimeout :: Lens' LintEnv Slot
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

_deposits :: Lens' LintEnv (Map (S.AccountId /\ S.Token) (Maybe BigInteger))
_deposits = _Newtype <<< prop (SProxy :: SProxy "deposits")

_isReachable :: Lens' LintEnv Boolean
_isReachable = _Newtype <<< prop (SProxy :: SProxy "isReachable")

emptyEnvironment :: List ContractPath -> LintEnv
emptyEnvironment unreachablePathList =
  LintEnv
    { choicesMade: mempty
    , deposits: mempty
    , letBindings: mempty
    , maxTimeout: mempty
    , isReachable: true
    , unreachablePaths: Just $ initializePrefixMap unreachablePathList
    }

-- Generic wrapper for stepPrefixMap. It steps the results of reachability analysis to see
-- if the current node is unreachable, if it is unreachable it calls `markUnreachable`
stepPrefixMapEnvGeneric :: LintEnv -> CMS.State State Unit -> ContractPathStep -> CMS.State State LintEnv
stepPrefixMapEnvGeneric (LintEnv env@{ unreachablePaths: Nothing }) markUnreachable cp = do
  pure $ LintEnv env { unreachablePaths = Nothing, isReachable = false }

stepPrefixMapEnvGeneric (LintEnv env@{ unreachablePaths: Just upOld, isReachable: oldReachable }) markUnreachable cp = do
  mUpNew <- stepPrefixMap markUnreachable upOld cp
  pure $ LintEnv env { unreachablePaths = mUpNew, isReachable = oldReachable && (not $ isNothing mUpNew) }

-- Wrapper for stepPrefixMap that marks unreachable code with a warning
stepPrefixMapEnv :: forall a. Show a => LintEnv -> a -> Location -> ContractPathStep -> CMS.State State LintEnv
stepPrefixMapEnv env t pos cp = stepPrefixMapEnvGeneric env markUnreachable cp
  where
  markUnreachable = addWarning UnreachableContract t pos

-- Simpler version of the wrapper for places for where we know we won't get a root of unreachable code
-- See isValidSubproblem in Reachability.purs for a list of roots of possible unreachable nodes
stepPrefixMapEnv_ :: LintEnv -> ContractPathStep -> CMS.State State LintEnv
stepPrefixMapEnv_ env cp = stepPrefixMapEnvGeneric env dontMarkUnreachable cp
  where
  dontMarkUnreachable = pure unit

data TemporarySimplification a b
  = ConstantSimp
    Location
    Boolean -- Is simplified (it is not just a constant that was already a constant)
    a -- Constant
  | ValueSimp
    Location
    Boolean -- Is simplified (only root, no subtrees)
    (Term b) -- Value

getSimpRange :: forall a b. TemporarySimplification a b -> Location
getSimpRange (ConstantSimp pos _ _) = pos

getSimpRange (ValueSimp pos _ _) = pos

isSimplified :: forall a b. TemporarySimplification a b -> Boolean
isSimplified (ConstantSimp _ simp _) = simp

isSimplified (ValueSimp _ simp _) = simp

getValue :: forall a b. (a -> Term b) -> TemporarySimplification a b -> Term b
getValue f (ConstantSimp _ _ c) = f c

getValue _ (ValueSimp _ _ v) = v

simplifyTo :: forall a b. TemporarySimplification a b -> Location -> TemporarySimplification a b
simplifyTo (ConstantSimp _ _ c) pos = (ConstantSimp pos true c)

simplifyTo (ValueSimp _ _ c) pos = (ValueSimp pos true c)

simplifyRefactoring :: Term Value -> Term Value -> Maybe TextEdit
simplifyRefactoring (Term _ (Range range)) to =
  let
    pv = show $ pretty to

    text = if hasArgs to then "(" <> pv <> ")" else pv
  in
    Just { range, text }

simplifyRefactoring _ _ = Nothing

addWarning :: forall a. Show a => WarningDetail -> a -> Location -> CMS.State State Unit
addWarning warnDetail term location =
  let
    refactoring = case warnDetail of
      (SimplifiableValue from to) -> simplifyRefactoring from to
      _ -> Nothing
  in
    modifying _warnings $ Set.insert
      $ Warning
          { warning: warnDetail
          , location
          , refactoring
          }

markSimplification :: forall a b. Show b => (a -> Term b) -> (Term b -> Term b -> WarningDetail) -> Term b -> TemporarySimplification a b -> CMS.State State Unit
markSimplification f c oriVal x
  | isSimplified x = addWarning (c oriVal (getValue f x)) oriVal (getLocation oriVal)
  | otherwise = pure unit

constToObs :: Boolean -> Term Observation
constToObs true = Term TrueObs NoLocation

constToObs false = Term FalseObs NoLocation

constToVal :: BigInteger -> Term Value
constToVal x = Term (Constant x) NoLocation

addMoneyToEnvAccount :: BigInteger -> S.AccountId -> S.Token -> LintEnv -> LintEnv
addMoneyToEnvAccount amountToAdd accTerm tokenTerm = over _deposits (Map.alter (addMoney amountToAdd) (accTerm /\ tokenTerm))
  where
  addMoney :: BigInteger -> Maybe (Maybe BigInteger) -> Maybe (Maybe BigInteger)
  addMoney amount Nothing = Just (Just amount)

  addMoney amount (Just prevVal) = Just (maybe Nothing (Just <<< (\prev -> prev + amount)) prevVal)

-- Note on PR https://github.com/input-output-hk/plutus/pull/2560:
--    Before PR 2560 which splitted the Simulation from the Marlowe Editor, the lint function was called on each step
--    of the simulation with the state as a parameter. That way, we could take past actions into account. Once we
--    split the two pages, we decided to only lint on the Marlowe Editor using the full contract, and for that reason
--    we removed the state from the code.
--    In the JIRA ticket SCP-1641 we captured the intent of doing a mid simulation analysis, as it could be one way
--    to cope with the problem of the STM only retrieving the first error. If we bring back that functionality, we may
--    want to add the state once again, and the Marlowe Editor should probably use the empty state to indicate no past
--    actions have been made.
--
-- FIXME: There is a bug where if you create holes with the same name in different When blocks they are missing from
--        the final lint result. After debugging it's strange because they seem to exist in intermediate states.
--
-- | We lint through a contract term collecting all warnings and holes etc so that we can display them in the editor
-- | The aim here is to only traverse the contract once since we are concerned about performance with the linting
lint :: List ContractPath -> Term Contract -> State
lint unreachablePaths contract =
  let
    env = emptyEnvironment unreachablePaths
  in
    CMS.execState (lintContract env contract) mempty

lintContract :: LintEnv -> Term Contract -> CMS.State State Unit
lintContract env (Term Close _) = pure unit

lintContract env t@(Term (Pay acc payee token payment cont) pos) = do
  addRoleFromPartyTerm acc
  case payee of
    Term (Account party) _ -> addRoleFromPartyTerm party
    Term (Party party) _ -> addRoleFromPartyTerm party
    _ -> pure unit
  modifying _holes (getHoles acc <> getHoles payee <> getHoles token) -- First we calculate the value and warn for non positive values
  sa <- lintValue env payment
  payedValue <- case sa of
    (ConstantSimp _ _ c)
      | c <= zero -> do
        addWarning NegativePayment t pos
        pure (Just zero)
      | otherwise -> pure (Just c)
    _ -> pure Nothing
  markSimplification constToVal SimplifiableValue payment sa
  tmpEnv /\ actualPaidMoney <- case fromTerm acc /\ fromTerm token of -- Second we account for withdrawing money from source account (using the info we know)
    Just accTerm /\ Just tokenTerm -> do -- We know source account
      let
        deposits = view _deposits env

        key = accTerm /\ tokenTerm
      newSrcAccVal /\ actualPaidMoney <- case Map.lookup key deposits /\ payedValue of
        Just (Just avMoney) /\ Just paidMoney ->  -- We know exactly what is happening (everything is constant)
          if (avMoney >= paidMoney) then
            pure $ Just (Just (avMoney - paidMoney)) /\ Just paidMoney
          else do
            addWarning (PartialPayment accTerm tokenTerm avMoney paidMoney) t pos
            pure $ Just (Just zero) /\ Just avMoney
        Nothing /\ _ -> do
          addWarning (PayBeforeDeposit accTerm) t pos -- There is definitely no money in that account
          pure $ Nothing /\ Nothing
        _ -> pure $ Just Nothing /\ Nothing -- We don't know how much is left in the account nor how much was paid
      let
        tmpEnv = over _deposits (Map.alter (const newSrcAccVal) key) env -- We set the source account with what we know
      pure $ tmpEnv /\ actualPaidMoney
    _ -> pure $ env /\ Nothing -- We don't know source account and thus we don't know how much was withdrawn either
  let
    tmpDeposits = view _deposits tmpEnv

    fixTargetAcc = case fromTerm payee /\ fromTerm token of -- Thirdly, if target is an account we account for adding money to it
      Just (EM.Account newAcc) /\ Just tokenTerm ->
        let
          destKey = newAcc /\ tokenTerm
        in
          Map.insert destKey case Map.lookup destKey tmpDeposits /\ actualPaidMoney of
            Just (Just avMoney) /\ Just paidMoney -> Just (avMoney + paidMoney) -- We know exactly what is happening (everything is constant)
            Nothing /\ Just paidMoney -> Just paidMoney -- We still know what is happening (there was no money, now there is)
            _ -> Nothing -- Either we don't know how much money there was or how money we are adding or both (so we don't know how much there will be)
      _ -> identity -- Either is not an account or we don't know so we do nothing     

    tmpEnv2 = over _deposits fixTargetAcc tmpEnv
  newEnv <- stepPrefixMapEnv_ tmpEnv2 PayContPath
  lintContract newEnv cont

lintContract env (Term (If obs c1 c2) _) = do
  sa <- lintObservation env obs
  c1Env <- stepPrefixMapEnv env c1 (getLocation c1) IfTruePath
  c2Env <- stepPrefixMapEnv env c2 (getLocation c2) IfFalsePath
  let
    reachable = view _isReachable

    c1Reachable = reachable c1Env

    c2Reachable = reachable c2Env

    updateEnv lEnv reach = if reach then lEnv else set _isReachable false lEnv
  c1NewEnv /\ c2NewEnv <-
    bimap (updateEnv c1Env) (updateEnv c2Env)
      <$> ( case sa of
            (ConstantSimp _ _ c) ->
              if c then do
                when c2Reachable $ addWarning UnreachableContract c2 (getLocation c2)
                pure (c1Reachable /\ false)
              else do
                when c1Reachable $ addWarning UnreachableContract c1 (getLocation c1)
                pure (false /\ c2Reachable)
            _ -> do
              markSimplification constToObs SimplifiableObservation obs sa
              pure (c1Reachable /\ c2Reachable)
        )
  lintContract c1NewEnv c1
  lintContract c2NewEnv c2

lintContract env (Term (When cases (Term (Holes.Slot timeout) pos) cont) _) = do
  when (Slot timeout <= view _maxTimeout env) (addWarning TimeoutNotIncreasing timeout pos)
  let
    tmpEnv = (over _maxTimeout (max $ Slot timeout)) env
  traverseWithIndex_ (lintCase tmpEnv) cases
  newEnv <- stepPrefixMapEnv_ tmpEnv WhenTimeoutPath
  lintContract newEnv cont
  pure unit

lintContract env (Term (When cases t cont) _) = do
  case t of
    Term (Holes.SlotParam slotParamName) _ -> addSlotParameter slotParamName
    _ -> pure unit
  modifying _holes (insertHole t)
  traverseWithIndex_ (lintCase env) cases
  newEnv <- stepPrefixMapEnv_ env WhenTimeoutPath
  lintContract newEnv cont
  pure unit

lintContract env (Term (Let (TermWrapper valueId pos) value cont) _) = do
  tmpEnv <- case fromTerm valueId of
    Just valueIdSem -> do
      let
        tmpEnv = over _letBindings (Set.insert valueIdSem) env
      when (Set.member valueIdSem (view _letBindings env)) $ addWarning ShadowedLet valueId pos
      pure tmpEnv
    Nothing -> pure env
  sa <- lintValue env value
  markSimplification constToVal SimplifiableValue value sa
  newEnv <- stepPrefixMapEnv_ tmpEnv LetPath
  lintContract newEnv cont

lintContract env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintContract env (Term (Assert obs cont) _) = do
  sa <- lintObservation env obs
  newEnv <- stepPrefixMapEnv_ env AssertPath
  lintContract newEnv cont
  markSimplification constToObs SimplifiableObservation obs sa
  pure unit

lintObservation :: LintEnv -> Term Observation -> CMS.State State (TemporarySimplification Boolean Observation)
lintObservation env t@(Term (AndObs a b) pos) = do
  sa <- lintObservation env a
  sb <- lintObservation env b
  case sa /\ sb of
    (ConstantSimp _ _ v /\ _) -> pure (if v then simplifyTo sb pos else ConstantSimp pos true false)
    (_ /\ ConstantSimp _ _ v) -> pure (if v then simplifyTo sa pos else ConstantSimp pos true false)
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      markSimplification constToObs SimplifiableObservation b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (OrObs a b) pos) = do
  sa <- lintObservation env a
  sb <- lintObservation env b
  case sa /\ sb of
    (ConstantSimp _ _ v /\ _) -> pure (if v then ConstantSimp pos true true else simplifyTo sb pos)
    (_ /\ ConstantSimp _ _ v) -> pure (if v then ConstantSimp pos true true else simplifyTo sa pos)
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      markSimplification constToObs SimplifiableObservation b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (NotObs a) pos) = do
  sa <- lintObservation env a
  case sa of
    (ConstantSimp _ _ c) -> pure (ConstantSimp pos true (not c))
    _ -> do
      markSimplification constToObs SimplifiableObservation a sa
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ChoseSomething choiceId@(ChoiceId choiceName party)) pos) = do
  addChoiceName choiceName
  addRoleFromPartyTerm party
  modifying _holes (getHoles choiceId)
  pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueGE a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 >= c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueGT a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 > c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueLT a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 < c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueLE a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 <= c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term (ValueEQ a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ c1 /\ ConstantSimp _ _ c2) -> pure (ConstantSimp pos true (c1 == c2))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintObservation env t@(Term TrueObs pos) = pure (ConstantSimp pos false true)

lintObservation env t@(Term FalseObs pos) = pure (ConstantSimp pos false false)

lintObservation env hole@(Hole _ _ pos) = do
  modifying _holes (insertHole hole)
  pure (ValueSimp pos false hole)

lintValue :: LintEnv -> Term Value -> CMS.State State (TemporarySimplification BigInteger Value)
lintValue env t@(Term (AvailableMoney acc token) pos) = do
  addRoleFromPartyTerm acc
  let
    gatherHoles = getHoles acc <> getHoles token
  modifying _holes gatherHoles
  pure (ValueSimp pos false t)

lintValue env (Term (Constant v) pos) = pure (ConstantSimp pos false v)

lintValue env t@(Term (ConstantParam str) pos) = do
  addValueParameter str
  pure (ValueSimp pos false t)

lintValue env t@(Term (NegValue a) pos) = do
  sa <- lintValue env a
  case sa of
    ConstantSimp _ _ c1 -> pure (ConstantSimp pos true (-c1))
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      pure (ValueSimp pos false t)

lintValue env t@(Term (AddValue a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2) -> pure (ConstantSimp pos true (v1 + v2))
    (ConstantSimp _ _ v /\ _)
      | v == zero -> pure (simplifyTo sb pos)
    (_ /\ ConstantSimp _ _ v)
      | v == zero -> pure (simplifyTo sa pos)
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintValue env t@(Term (SubValue a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2) -> pure (ConstantSimp pos true (v1 - v2))
    (ConstantSimp _ _ v /\ _)
      | v == zero -> pure (ValueSimp pos true (Term (NegValue b) pos))
    (_ /\ ConstantSimp _ _ v)
      | v == zero -> pure (simplifyTo sa pos)
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintValue env t@(Term (MulValue a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  case sa /\ sb of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2) -> pure (ConstantSimp pos true (v1 * v2))
    (ConstantSimp _ _ v /\ _)
      | v == zero -> pure (ConstantSimp pos true zero)
    (_ /\ ConstantSimp _ _ v)
      | v == zero -> pure (ConstantSimp pos true zero)
    (ConstantSimp _ _ v /\ _)
      | v == one -> pure (simplifyTo sb pos)
    (_ /\ ConstantSimp _ _ v)
      | v == one -> pure (simplifyTo sa pos)
    _ -> do
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

lintValue env t@(Term (Scale (TermWrapper r@(Rational a b) pos2) c) pos) = do
  sc <- lintValue env c
  if (b == zero) then do
    addWarning DivisionByZero r pos2
    markSimplification constToVal SimplifiableValue c sc
    pure (ValueSimp pos false t)
  else
    let
      gcdv = gcd a b

      na = a `div` gcdv

      nb = b `div` gcdv

      isSimp = (abs gcdv) > one
    in
      case sc of
        (ConstantSimp _ _ v) -> pure (ConstantSimp pos true (evalValue (makeEnvironment zero zero) (emptyState (Slot zero)) (S.Scale (S.Rational a b) (S.Constant v))))
        (ValueSimp _ _ v) -> do
          if isSimp then
            pure unit
          else do
            markSimplification constToVal SimplifiableValue c sc
          pure (ValueSimp pos isSimp (Term (Scale (TermWrapper (Rational na nb) pos2) c) pos))

lintValue env t@(Term (ChoiceValue choiceId@(ChoiceId choiceName party)) pos) = do
  addChoiceName choiceName
  addRoleFromPartyTerm party
  when
    ( case fromTerm choiceId of
        Just semChoiceId -> not $ Set.member semChoiceId (view _choicesMade env)
        Nothing -> false
    )
    (addWarning UndefinedChoice t pos)
  modifying _holes (getHoles choiceId)
  pure (ValueSimp pos false t)

lintValue env t@(Term SlotIntervalStart pos) = pure (ValueSimp pos false t)

lintValue env t@(Term SlotIntervalEnd pos) = pure (ValueSimp pos false t)

lintValue env t@(Term (UseValue (TermWrapper valueId _)) pos) = do
  when
    ( case fromTerm valueId of
        Just semValueId -> not $ Set.member semValueId (view _letBindings env)
        Nothing -> false
    )
    (addWarning UndefinedUse t pos)
  pure (ValueSimp pos false t)

lintValue env hole@(Hole _ _ pos) = do
  modifying _holes (insertHole hole)
  pure (ValueSimp pos false hole)

lintValue env t@(Term (Cond c a b) pos) = do
  sa <- lintValue env a
  sb <- lintValue env b
  sc <- lintObservation env c
  case sa /\ sb /\ sc of
    (ConstantSimp _ _ v1 /\ ConstantSimp _ _ v2 /\ ConstantSimp _ _ vc) -> pure (ConstantSimp pos true if vc then v1 else v2)
    (_ /\ _ /\ ConstantSimp _ _ vc)
      | vc -> pure (simplifyTo sa pos)
    (_ /\ _ /\ ConstantSimp _ _ vc)
      | not vc -> pure (simplifyTo sb pos)
    _ -> do
      markSimplification constToObs SimplifiableObservation c sc
      markSimplification constToVal SimplifiableValue a sa
      markSimplification constToVal SimplifiableValue b sb
      pure (ValueSimp pos false t)

data Effect
  = ConstantDeposit S.AccountId S.Token BigInteger
  | UnknownDeposit S.AccountId S.Token
  | ChoiceMade S.ChoiceId
  | NoEffect

lintCase :: LintEnv -> Int -> Term Case -> CMS.State State Unit
lintCase iniEnv n t@(Term (Case action contract) pos) = do
  env <- stepPrefixMapEnv iniEnv t pos $ WhenCasePath n
  effect /\ isReachable <- lintAction env action
  let
    tempEnv = case effect of
      ConstantDeposit accTerm tokenTerm amount -> addMoneyToEnvAccount amount accTerm tokenTerm env
      UnknownDeposit accTerm tokenTerm -> over _deposits (Map.insert (accTerm /\ tokenTerm) Nothing) env
      ChoiceMade choiceId -> over _choicesMade (Set.insert choiceId) env
      NoEffect -> env

    newEnv = set _isReachable isReachable tempEnv
  lintContract newEnv contract
  pure unit

lintCase env n hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintBounds :: Boolean -> Term Bound -> CMS.State State Boolean
lintBounds restAreInvalid t@(Hole _ _ _) = do
  pure false

lintBounds restAreInvalid t@(Term (Bound l h) pos) = do
  let
    isInvalidBound = l > h
  when isInvalidBound $ addWarning InvalidBound t pos
  pure (isInvalidBound && restAreInvalid)

lintAction :: LintEnv -> Term Action -> CMS.State State (Effect /\ Boolean) -- Booleans says whether the action is reachable
lintAction env t@(Term (Deposit acc party token value) pos) = do
  let
    accTerm = maybe NoEffect (maybe (const NoEffect) UnknownDeposit (fromTerm acc)) (fromTerm token)

    isReachable = view _isReachable env
  addRoleFromPartyTerm acc
  addRoleFromPartyTerm party
  modifying _holes (getHoles acc <> getHoles party <> getHoles token)
  sa <- lintValue env value
  (\effect -> effect /\ isReachable)
    <$> case sa of
        (ConstantSimp _ _ v)
          | v <= zero -> do
            addWarning NegativeDeposit t pos
            pure (makeDepositConstant accTerm zero)
          | otherwise -> do
            markSimplification constToVal SimplifiableValue value sa
            pure (makeDepositConstant accTerm v)
        _ -> do
          markSimplification constToVal SimplifiableValue value sa
          pure accTerm
  where
  makeDepositConstant (UnknownDeposit ac to) v = ConstantDeposit ac to v

  makeDepositConstant other _ = other

lintAction env t@(Term (Choice choiceId@(ChoiceId choiceName party) bounds) pos) = do
  let
    choTerm = maybe NoEffect ChoiceMade (fromTerm choiceId)

    isReachable = view _isReachable env
  addChoiceName choiceName
  addRoleFromPartyTerm party
  modifying _holes (getHoles choiceId <> getHoles bounds)
  allInvalid <- foldM lintBounds true bounds
  when (allInvalid && isReachable) $ addWarning UnreachableCaseEmptyChoice t pos
  pure $ choTerm /\ (not allInvalid && isReachable)

lintAction env t@(Term (Notify obs) pos) = do
  let
    isReachable = view _isReachable env
  sa <- lintObservation env obs
  newIsReachable <- case sa of
    (ConstantSimp _ _ c)
      | not c -> do
        when isReachable $ addWarning UnreachableCaseFalseNotify t pos
        pure false
    _ -> do
      markSimplification constToObs SimplifiableObservation obs sa
      pure isReachable
  pure $ NoEffect /\ newIsReachable

lintAction env hole@(Hole _ _ _) = do
  let
    isReachable = view _isReachable env
  modifying _holes (insertHole hole)
  pure $ NoEffect /\ isReachable
