module Marlowe.Linter
  ( lint
  , State(..)
  , MaxTimeout
  , Warning(..)
  , WarningDetail(..)
  , AdditionalContext
  , _holes
  , _warnings
  , suggestions
  , markers
  , format
  , provideCodeActions
  , getWarningRange
  ) where

import Prelude
import Control.Monad.State as CMS
import Data.Array (catMaybes, fold, foldMap, take)
import Data.Array as Array
import Data.Array.NonEmpty (index)
import Data.Bifunctor (bimap)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), hush)
import Data.Foldable (foldM)
import Data.Function (on)
import Data.Functor (mapFlipped)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', modifying, over, set, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.List (List(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing, maybe)
import Data.Newtype (class Newtype)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.String (codePointFromChar, fromCodePointArray, length, takeWhile, toCodePointArray)
import Data.String.Regex (match, regex)
import Data.String.Regex.Flags (noFlags)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse_)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Help (holeText)
import Marlowe.Holes (Action(..), Argument, Bound(..), Case(..), Contract(..), Holes(..), MarloweHole(..), MarloweType, Observation(..), Term(..), TermWrapper(..), Value(..), Range, constructMarloweType, fromTerm, getHoles, getMarloweConstructors, getRange, holeSuggestions, insertHole, readMarloweType)
import Marlowe.Parser (ContractParseError(..), parseContract)
import Marlowe.Semantics (Rational(..), Slot(..), _accounts, _boundValues, _choices, emptyState, evalValue, makeEnvironment)
import Marlowe.Semantics as Semantics
import Monaco (CodeAction, CompletionItem, IMarkerData, IRange, TextEdit, Uri, markerSeverity)
import Monaco as Monaco
import Reachability (initialisePrefixMap, stepPrefixMap)
import Simulation.Types (ContractPath, ContractPathStep, PrefixMap)
import Text.Pretty (hasArgs, pretty)

newtype MaxTimeout
  = MaxTimeout (TermWrapper Slot)

derive instance newtypeMaxTimeout :: Newtype MaxTimeout _

derive newtype instance eqMaxTimeout :: Eq MaxTimeout

derive newtype instance ordMaxTimeout :: Ord MaxTimeout

instance semigroupMax :: Semigroup MaxTimeout where
  append a b = max a b

instance monoidMaxTimeout :: Monoid MaxTimeout where
  mempty = MaxTimeout (TermWrapper zero zero)

newtype Warning
  = Warning
  { warning :: WarningDetail
  , range :: IRange
  , refactoring :: Maybe TextEdit
  }

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
  | PayBeforeDeposit Semantics.AccountId
  | PartialPayment Semantics.AccountId Semantics.Token BigInteger BigInteger

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
  show (PayBeforeDeposit account) = "The contract makes a payment from account " <> show account <> " before a deposit has been made"
  show (PartialPayment accountId tokenId availableAmount demandedAmount) =
    "The contract makes a payment of " <> show demandedAmount <> " "
      <> show tokenId
      <> " from account "
      <> show accountId
      <> " but the account only has "
      <> show availableAmount

shortWarning :: WarningDetail -> String
shortWarning NegativePayment = ""

shortWarning NegativeDeposit = ""

shortWarning TimeoutNotIncreasing = ""

shortWarning UnreachableCaseEmptyChoice = ""

shortWarning InvalidBound = ""

shortWarning UnreachableCaseFalseNotify = ""

shortWarning UnreachableContract = ""

shortWarning UndefinedChoice = ""

shortWarning UndefinedUse = ""

shortWarning ShadowedLet = ""

shortWarning DivisionByZero = ""

shortWarning (SimplifiableValue _ _) = "Simplify Value"

shortWarning (SimplifiableObservation _ _) = ""

shortWarning (PayBeforeDeposit _) = ""

shortWarning (PartialPayment _ _ _ _) = ""

warningType :: Warning -> String
warningType (Warning { warning }) = case warning of
  NegativePayment -> "NegativePayment"
  NegativeDeposit -> "NegativeDeposit"
  TimeoutNotIncreasing -> "TimeoutNotIncreasing"
  UnreachableCaseEmptyChoice -> "UnreachableCaseEmptyChoice"
  InvalidBound -> "InvalidBound"
  UnreachableCaseFalseNotify -> "UnreachableCaseFalseNotify"
  UnreachableContract -> "UnreachableContract"
  UndefinedChoice -> "UndefinedChoice"
  UndefinedUse -> "UndefinedUse"
  ShadowedLet -> "ShadowedLet"
  DivisionByZero -> "DivisionByZero"
  (SimplifiableValue _ _) -> "SimplifiableValue"
  (SimplifiableObservation _ _) -> "SimplifiableObservation"
  (PayBeforeDeposit _) -> "PayBeforeDeposit"
  (PartialPayment _ _ _ _) -> "PartialPayment"

derive instance genericWarningDetail :: Generic WarningDetail _

instance eqWarningDetail :: Eq WarningDetail where
  eq = genericEq

instance ordWarningDetail :: Ord WarningDetail where
  compare = genericCompare

derive instance genericWarning :: Generic Warning _

instance eqWarning :: Eq Warning where
  eq = genericEq

-- We order Warnings by their Range first
instance ordWarning :: Ord Warning where
  compare a@(Warning { range: rangeA }) b@(Warning { range: rangeB }) =
    let
      cmp f = (compare `on` f) rangeA rangeB
    in
      case cmp _.startLineNumber, cmp _.startColumn, cmp _.endLineNumber, cmp _.endColumn of
        EQ, EQ, EQ, elc -> genericCompare a b
        EQ, EQ, eln, _ -> eln
        EQ, slc, _, _ -> slc
        sln, _, _, _ -> sln

instance showWarning :: Show Warning where
  show (Warning warn) = show warn.warning

getWarningRange :: Warning -> IRange
getWarningRange (Warning warn) = warn.range

newtype State
  = State
  { holes :: Holes
  , warnings :: Set Warning
  }

derive instance newtypeState :: Newtype State _

derive newtype instance semigroupState :: Semigroup State

derive newtype instance monoidState :: Monoid State

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_warnings :: Lens' State (Set Warning)
_warnings = _Newtype <<< prop (SProxy :: SProxy "warnings")

newtype LintEnv
  = LintEnv
  { choicesMade :: Set Semantics.ChoiceId
  , deposits :: Map (Semantics.AccountId /\ Semantics.Token) (Maybe BigInteger)
  , letBindings :: Set Semantics.ValueId
  , maxTimeout :: MaxTimeout
  , isReachable :: Boolean
  , unreachablePaths :: Maybe PrefixMap
  }

derive instance newtypeLintEnv :: Newtype LintEnv _

_choicesMade :: Lens' LintEnv (Set Semantics.ChoiceId)
_choicesMade = _Newtype <<< prop (SProxy :: SProxy "choicesMade")

_letBindings :: Lens' LintEnv (Set Semantics.ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

_maxTimeout :: Lens' LintEnv (TermWrapper Slot)
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

_deposits :: Lens' LintEnv (Map (Semantics.AccountId /\ Semantics.Token) (Maybe BigInteger))
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
    , unreachablePaths: Just $ initialisePrefixMap unreachablePathList
    }

stepPrefixMapEnv :: forall a. Show a => LintEnv -> a -> Range -> ContractPathStep -> CMS.State State LintEnv
stepPrefixMapEnv (LintEnv env@{ unreachablePaths: Nothing }) t pos cp = do
  pure $ LintEnv env { unreachablePaths = Nothing, isReachable = false }

stepPrefixMapEnv (LintEnv env@{ unreachablePaths: Just upOld }) t pos cp = do
  mUpNew <- stepPrefixMap markUnreachable upOld cp
  pure $ LintEnv env { unreachablePaths = mUpNew, isReachable = isNothing mUpNew }
  where
  markUnreachable = do addWarning UnreachableContract t pos

data TemporarySimplification a b
  = ConstantSimp
    Range
    Boolean -- Is simplified (it is not just a constant that was already a constant)
    a -- Constant
  | ValueSimp
    Range
    Boolean -- Is simplified (only root, no subtrees)
    (Term b) -- Value

getSimpRange :: forall a b. TemporarySimplification a b -> Range
getSimpRange (ConstantSimp pos _ _) = pos

getSimpRange (ValueSimp pos _ _) = pos

isSimplified :: forall a b. TemporarySimplification a b -> Boolean
isSimplified (ConstantSimp _ simp _) = simp

isSimplified (ValueSimp _ simp _) = simp

getValue :: forall a b. (a -> Term b) -> TemporarySimplification a b -> Term b
getValue f (ConstantSimp _ _ c) = f c

getValue _ (ValueSimp _ _ v) = v

simplifyTo :: forall a b. TemporarySimplification a b -> Range -> TemporarySimplification a b
simplifyTo (ConstantSimp _ _ c) pos = (ConstantSimp pos true c)

simplifyTo (ValueSimp _ _ c) pos = (ValueSimp pos true c)

simplifyRefactoring :: Term Value -> Term Value -> Maybe TextEdit
simplifyRefactoring (Term _ range) to =
  let
    pv = show $ pretty to

    text = if hasArgs to then "(" <> pv <> ")" else pv
  in
    Just { range, text }

simplifyRefactoring _ _ = Nothing

addWarning :: forall a. Show a => WarningDetail -> a -> Range -> CMS.State State Unit
addWarning warnDetail term range =
  let
    refactoring = case warnDetail of
      (SimplifiableValue from to) -> simplifyRefactoring from to
      _ -> Nothing
  in
    modifying _warnings $ Set.insert
      $ Warning
          { warning: warnDetail
          , range
          , refactoring
          }

markSimplification :: forall a b. Show b => (a -> Term b) -> (Term b -> Term b -> WarningDetail) -> Term b -> TemporarySimplification a b -> CMS.State State Unit
markSimplification f c oriVal x
  | isSimplified x = addWarning (c oriVal (getValue f x)) oriVal (getRange oriVal)
  | otherwise = pure unit

constToObs :: Boolean -> Term Observation
constToObs true = Term TrueObs zero

constToObs false = Term FalseObs zero

constToVal :: BigInteger -> Term Value
constToVal x = Term (Constant x) zero

addMoneyToEnvAccount :: BigInteger -> Semantics.AccountId -> Semantics.Token -> LintEnv -> LintEnv
addMoneyToEnvAccount amountToAdd accTerm tokenTerm = over _deposits (Map.alter (addMoney amountToAdd) (accTerm /\ tokenTerm))
  where
  addMoney :: BigInteger -> Maybe (Maybe BigInteger) -> Maybe (Maybe BigInteger)
  addMoney amount Nothing = Just (Just amount)

  addMoney amount (Just prevVal) = Just (maybe Nothing (Just <<< (\prev -> prev + amount)) prevVal)

-- | We lintContract through a contract term collecting all warnings and holes etc so that we can display them in the editor
-- | The aim here is to only traverse the contract once since we are concerned about performance with the linting
-- FIXME: There is a bug where if you create holes with the same name in different When blocks they are missing from
-- the final lint result. After debugging it's strange because they seem to exist in intermediate states.
lint :: List ContractPath -> Semantics.State -> Term Contract -> State
lint unreachablePaths contractState contract = state
  where
  choices = contractState ^. (_choices <<< to Map.keys)

  bindings = contractState ^. (_boundValues <<< to Map.keys)

  deposits = contractState ^. (_accounts <<< to (Map.mapMaybe (Just <<< Just)))

  env = (set _letBindings bindings <<< set _deposits deposits <<< set _choicesMade choices) (emptyEnvironment unreachablePaths)

  state = CMS.execState (lintContract env contract) mempty

lintContract :: LintEnv -> Term Contract -> CMS.State State Unit
lintContract env (Term Close _) = pure unit

lintContract env t@(Term (Pay acc payee token payment cont) pos) = do
  let
    gatherHoles = getHoles acc <> getHoles payee <> getHoles token
  modifying _holes gatherHoles
  sa <- lintValue env payment
  payedValue <- case sa of
    (ConstantSimp _ _ c)
      | c <= zero -> do
        addWarning NegativePayment t pos
        pure (Just zero)
      | otherwise -> pure (Just c)
    _ -> pure Nothing
  markSimplification constToVal SimplifiableValue payment sa
  newEnv <- case (fromTerm acc /\ fromTerm token) of
    Just accTerm /\ Just tokenTerm -> do
      let
        deposits = view _deposits env

        key = accTerm /\ tokenTerm
      unless (Map.member key deposits)
        (addWarning (PayBeforeDeposit accTerm) t pos)
      case (Map.lookup key deposits /\ payedValue) of
        (Just (Just avMoney)) /\ (Just paidMoney) -> do
          unless (avMoney >= paidMoney) (addWarning (PartialPayment accTerm tokenTerm avMoney paidMoney) t pos)
          let
            actualPaidMoney = min avMoney paidMoney
          let
            tempEnv = over _deposits (Map.insert key (Just (avMoney - actualPaidMoney))) env
          pure
            ( case fromTerm payee of
                Just (Semantics.Account newAcc) -> addMoneyToEnvAccount actualPaidMoney newAcc tokenTerm tempEnv
                _ -> tempEnv
            )
        Nothing /\ _ -> pure env
        _ -> pure (over _deposits (Map.insert key Nothing) env)
    _ -> pure env
  lintContract newEnv cont

lintContract env (Term (If obs c1 c2) _) = do
  sa <- lintObservation env obs
  let
    currReachable = view _isReachable env

    newEnv reach = if reach then env else set _isReachable false env
  c1Env /\ c2Env <-
    bimap newEnv newEnv
      <$> ( case sa of
            (ConstantSimp _ _ c) ->
              if c then do
                when currReachable $ addWarning UnreachableContract c2 (getRange c2)
                pure (currReachable /\ false)
              else do
                when currReachable $ addWarning UnreachableContract c1 (getRange c1)
                pure (false /\ currReachable)
            _ -> do
              markSimplification constToObs SimplifiableObservation obs sa
              pure (currReachable /\ currReachable)
        )
  lintContract c1Env c1
  lintContract c2Env c2

lintContract env (Term (When cases timeout@(TermWrapper slot pos) cont) _) = do
  let
    newEnv = (over _maxTimeout (max timeout)) env
  traverse_ (lintCase newEnv) cases
  when (timeout <= view _maxTimeout env) (addWarning TimeoutNotIncreasing slot pos)
  lintContract newEnv cont
  pure unit

lintContract env (Term (Let (TermWrapper valueId pos) value cont) _) = do
  newEnv <- case fromTerm valueId of
    Just valueIdSem -> do
      let
        newEnv = over _letBindings (Set.insert valueIdSem) env
      when (Set.member valueIdSem (view _letBindings env)) $ addWarning ShadowedLet valueId pos
      pure newEnv
    Nothing -> pure env
  sa <- lintValue env value
  markSimplification constToVal SimplifiableValue value sa
  lintContract newEnv cont

lintContract env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintContract env (Term (Assert obs cont) _) = do
  sa <- lintObservation env obs
  lintContract env cont
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

lintObservation env t@(Term (ChoseSomething choiceId) pos) = do
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
  let
    gatherHoles = getHoles acc <> getHoles token
  modifying _holes gatherHoles
  pure (ValueSimp pos false t)

lintValue env (Term (Constant v) pos) = pure (ConstantSimp pos false v)

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
        (ConstantSimp _ _ v) -> pure (ConstantSimp pos true (evalValue (makeEnvironment zero zero) (emptyState (Slot zero)) (Semantics.Scale (Semantics.Rational a b) (Semantics.Constant v))))
        (ValueSimp _ _ v) -> do
          if isSimp then
            pure unit
          else do
            markSimplification constToVal SimplifiableValue c sc
          pure (ValueSimp pos isSimp (Term (Scale (TermWrapper (Rational na nb) pos2) c) pos))

lintValue env t@(Term (ChoiceValue choiceId) pos) = do
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
  = ConstantDeposit Semantics.AccountId Semantics.Token BigInteger
  | UnknownDeposit Semantics.AccountId Semantics.Token
  | ChoiceMade Semantics.ChoiceId
  | NoEffect

lintCase :: LintEnv -> Term Case -> CMS.State State Unit
lintCase env t@(Term (Case action contract) pos) = do
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

lintCase env hole@(Hole _ _ _) = do
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

    gatherHoles = getHoles acc <> getHoles party <> getHoles token
  modifying _holes (gatherHoles)
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

lintAction env t@(Term (Choice choiceId bounds) pos) = do
  let
    choTerm = maybe NoEffect ChoiceMade (fromTerm choiceId)

    isReachable = view _isReachable env
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

type AdditionalContext
  = { warnings :: Set Warning
    , contract :: Maybe (Term Contract)
    }

suggestions :: String -> Boolean -> String -> IRange -> AdditionalContext -> Array CompletionItem
suggestions original stripParens contractString range { contract } =
  fromMaybe [] do
    -- there will be no contract if it had errors, this is no good because we want to try to fix this
    -- with contractString, which is a contract that comes from the MarloweCompletionItemProvider with
    -- holes where possible errors are, so it might be able to be parsed.
    parsedContract <- case contract of
      Nothing -> hush $ parseContract contractString
      c -> c
    let
      (Holes holes) = view _holes ((lint Nil (emptyState zero)) parsedContract)
    v <- Map.lookup "monaco_suggestions" holes
    { head } <- Array.uncons $ Set.toUnfoldable v
    pure $ holeSuggestions original stripParens range head

-- FIXME: We have multiple model markers, 1 per quick fix. This is wrong though, we need only 1 but in MarloweCodeActionProvider we want to run the code
-- to generate the quick fixes from this single model marker
markers :: List ContractPath -> Semantics.State -> String -> Tuple (Array IMarkerData) AdditionalContext
markers unreachablePaths contractState contract = do
  let
    parsedContract = parseContract contract
  case (lint unreachablePaths contractState <$> parsedContract) of
    Left EmptyInput -> (Tuple [] { warnings: mempty, contract: Nothing })
    Left e@(ContractParseError { message, row, column, token }) ->
      let
        whiteSpaceChar c = Set.member c $ Set.fromFoldable $ map codePointFromChar [ '\n', '\r', ' ', '\t' ]

        word = takeWhile (not <<< whiteSpaceChar) token

        markerData =
          [ { startColumn: column
            , startLineNumber: row
            , endColumn: column + (length word)
            , endLineNumber: row
            , message: message
            , severity: markerSeverity "Error"
            , code: ""
            , source: ""
            }
          ]
      in
        (Tuple markerData { warnings: mempty, contract: Nothing })
    Right state ->
      let
        holesMarkers = state ^. (_holes <<< to holesToMarkers)

        warningsMarkers = state ^. (_warnings <<< to Set.toUnfoldable <<< to (map warningToMarker))

        -- we store the current warnings and the parsed contract in the halogen state so that they can be reused
        additionalContext = { warnings: state ^. _warnings, contract: hush parsedContract }
      in
        (Tuple (holesMarkers <> warningsMarkers) additionalContext)

-- other types of warning could do with being refactored to a Warning ADT first so we don't need to repeat ourselves
holesToMarkers :: Holes -> Array IMarkerData
holesToMarkers (Holes holes) =
  let
    (allHoles :: Array _) = Set.toUnfoldable $ fold $ Map.values holes
  in
    foldMap holeToMarkers allHoles

holeToMarker :: MarloweHole -> Map String (Array Argument) -> String -> IMarkerData
holeToMarker hole@(MarloweHole { name, marloweType, range: { startLineNumber, startColumn, endLineNumber, endColumn } }) m constructorName =
  { startColumn
  , startLineNumber
  , endColumn
  , endLineNumber
  , message: holeText marloweType
  , severity: markerSeverity "Warning"
  , code: ""
  , source: "Hole: " <> (dropEnd 4 $ show marloweType)
  }
  where
  dropEnd :: Int -> String -> String
  dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray

holeToMarkers :: MarloweHole -> Array IMarkerData
holeToMarkers hole@(MarloweHole { name, marloweType }) =
  let
    m = getMarloweConstructors marloweType

    constructors = take 1 $ Set.toUnfoldable $ Map.keys m
  in
    map (holeToMarker hole m) constructors

markerToHole :: IMarkerData -> MarloweType -> MarloweHole
markerToHole markerData marloweType = MarloweHole { name: "unknown", marloweType, range: (Monaco.getRange markerData) }

warningToMarker :: Warning -> IMarkerData
warningToMarker warning =
  let
    { startColumn, startLineNumber, endColumn, endLineNumber } = getWarningRange warning
  in
    { startColumn
    , startLineNumber
    , endColumn
    , endLineNumber
    , message: show warning
    , severity: markerSeverity "Warning"
    , code: ""
    , source: warningType warning
    }

format :: String -> String
format contractString = case parseContract contractString of
  Left _ -> contractString
  Right contract -> show $ pretty contract

provideLintCodeActions :: Uri -> AdditionalContext -> Array CodeAction
provideLintCodeActions uri { warnings } = catMaybes <<< map codeAction <<< Set.toUnfoldable $ warnings
  where
  codeAction :: Warning -> Maybe CodeAction
  codeAction (Warning { warning, range, refactoring: Just refactoring }) =
    Just
      { title: shortWarning warning
      , edit: { edits: [ { resource: uri, edit: refactoring } ] }
      , kind: "quickfix"
      }

  codeAction _ = Nothing

provideCodeActions :: Uri -> Array IMarkerData -> AdditionalContext -> Array CodeAction
provideCodeActions uri markers' additionalContext =
  provideLintCodeActions uri additionalContext
    <> (flip foldMap) markers' \(marker@{ source, startLineNumber, startColumn, endLineNumber, endColumn }) -> case regex "Hole: (\\w+)" noFlags of
        Left _ -> []
        Right r -> case readMarloweType =<< (join <<< (flip index 1)) =<< match r (source <> "Type") of
          Nothing -> []
          Just marloweType ->
            let
              m = getMarloweConstructors marloweType

              hole = markerToHole marker marloweType

              (constructors :: Array _) = Set.toUnfoldable $ Map.keys m

              range =
                { startLineNumber
                , startColumn
                , endLineNumber
                , endColumn
                }

              actions =
                mapFlipped constructors \constructorName ->
                  let
                    text = constructMarloweType constructorName hole m

                    edit = { resource: uri, edit: { range, text } }
                  in
                    { title: constructorName, edit: { edits: [ edit ] }, kind: "quickfix" }
            in
              actions
