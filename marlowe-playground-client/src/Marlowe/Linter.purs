module Marlowe.Linter
  ( lint
  , State(..)
  , Position
  , MaxTimeout
  , Warning(..)
  , WarningDetail(..)
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
import Data.Array (fold, foldMap, take)
import Data.Array as Array
import Data.Array.NonEmpty (index)
import Data.BigInteger (BigInteger)
import Data.Either (Either(..), hush)
import Data.Function (on)
import Data.Functor (mapFlipped)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', modifying, over, set, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Ord (abs)
import Data.Set (Set)
import Data.Set as Set
import Data.String (codePointFromChar, fromCodePointArray, length, takeWhile, toCodePointArray)
import Data.String.Regex (match, regex)
import Data.String.Regex.Flags (noFlags)
import Data.Symbol (SProxy(..))
import Data.Traversable (traverse_)
import Data.Tuple.Nested (type (/\), (/\))
import Help (holeText)
import Marlowe.Holes (Action(..), Argument, Case(..), Contract(..), Holes(..), MarloweHole(..), MarloweType, Observation(..), Term(..), TermWrapper(..), Value(..), ValueId, constructMarloweType, fromTerm, getHoles, getMarloweConstructors, getPosition, holeSuggestions, insertHole, readMarloweType)
import Marlowe.Parser (ContractParseError(..), parseContract)
import Marlowe.Semantics (Rational(..), Slot(..), _accounts, _boundValues, emptyState, evalValue, makeEnvironment)
import Marlowe.Semantics as Semantics
import Monaco (CodeAction, CompletionItem, IMarkerData, Uri, IRange, markerSeverity)
import Text.Parsing.StringParser (Pos)
import Text.Pretty (pretty)

type Position
  = { row :: Pos, column :: Pos }

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
  }

data WarningDetail
  = NegativePayment
  | NegativeDeposit
  | TimeoutNotIncreasing
  | UnreachableCaseEmptyChoice
  | UnreachableCaseFalseNotify
  | UnreachableContract
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
  show UnreachableCaseEmptyChoice = "This case will never be used, because there are no options to choose"
  show UnreachableCaseFalseNotify = "This case will never be used, because the Observation is always false"
  show UnreachableContract = "This contract is unreachable"
  show UndefinedUse = "The contract tries to Use a ValueId that has not been defined in a Let"
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

derive instance genericWarningDetail :: Generic WarningDetail _

instance eqWarningDetail :: Eq WarningDetail where
  eq = genericEq

instance ordWarningDetail :: Ord WarningDetail where
  compare = genericCompare

derive instance genericWarning :: Generic Warning _

instance eqWarning :: Eq Warning where
  eq = genericEq

-- We order Warnings by their position first
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
  , maxTimeout :: MaxTimeout
  , letBindings :: Set ValueId
  , warnings :: Set Warning
  }

derive instance newtypeState :: Newtype State _

derive newtype instance semigroupState :: Semigroup State

derive newtype instance monoidState :: Monoid State

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_warnings :: Lens' State (Set Warning)
_warnings = _Newtype <<< prop (SProxy :: SProxy "warnings")

termToRange :: forall a. Show a => a -> { row :: Int, column :: Int } -> IRange
termToRange a { row, column } =
  { startLineNumber: row
  , startColumn: column
  , endLineNumber: row
  , endColumn: column + (length (show a))
  }

newtype LintEnv
  = LintEnv
  { letBindings :: Set Semantics.ValueId
  , maxTimeout :: MaxTimeout
  , deposits :: Map (Semantics.AccountId /\ Semantics.Token) (Maybe BigInteger)
  }

derive instance newtypeLintEnv :: Newtype LintEnv _

derive newtype instance semigroupLintEnv :: Semigroup LintEnv

derive newtype instance monoidLintEnv :: Monoid LintEnv

_letBindings :: Lens' LintEnv (Set Semantics.ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

_maxTimeout :: Lens' LintEnv (TermWrapper Slot)
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

_deposits :: Lens' LintEnv (Map (Semantics.AccountId /\ Semantics.Token) (Maybe BigInteger))
_deposits = _Newtype <<< prop (SProxy :: SProxy "deposits")

data TemporarySimplification a b
  = ConstantSimp
    Position
    Boolean -- Is simplified (it is not just a constant that was already a constant)
    a -- Constant
  | ValueSimp
    Position
    Boolean -- Is simplified (only root, no subtrees)
    (Term b) -- Value

getSimpPosition :: forall a b. TemporarySimplification a b -> Position
getSimpPosition (ConstantSimp pos _ _) = pos

getSimpPosition (ValueSimp pos _ _) = pos

isSimplified :: forall a b. TemporarySimplification a b -> Boolean
isSimplified (ConstantSimp _ simp _) = simp

isSimplified (ValueSimp _ simp _) = simp

getValue :: forall a b. (a -> Term b) -> TemporarySimplification a b -> Term b
getValue f (ConstantSimp _ _ c) = f c

getValue _ (ValueSimp _ _ v) = v

simplifyTo :: forall a b. TemporarySimplification a b -> Position -> TemporarySimplification a b
simplifyTo (ConstantSimp _ _ c) pos = (ConstantSimp pos true c)

simplifyTo (ValueSimp _ _ c) pos = (ValueSimp pos true c)

addWarning :: forall a. Show a => WarningDetail -> a -> { row :: Int, column :: Int } -> CMS.State State Unit
addWarning warnDetail term pos =
  modifying _warnings $ Set.insert
    $ Warning
        { warning: warnDetail
        , range: termToRange term pos
        }

markSimplification :: forall a b. Show b => (a -> Term b) -> (Term b -> Term b -> WarningDetail) -> Term b -> TemporarySimplification a b -> CMS.State State Unit
markSimplification f c oriVal x
  | isSimplified x = addWarning (c oriVal (getValue f x)) oriVal (getPosition oriVal)
  | otherwise = pure unit

constToObs :: Boolean -> Term Observation
constToObs true = Term TrueObs { row: 0, column: 0 }

constToObs false = Term FalseObs { row: 0, column: 0 }

constToVal :: BigInteger -> Term Value
constToVal x = Term (Constant x) { row: 0, column: 0 }

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
lint :: Semantics.State -> Term Contract -> State
lint contractState contract = state
  where
  deposits = contractState ^. (_accounts <<< to (Map.mapMaybe (Just <<< Just)))

  bindings = contractState ^. (_boundValues <<< to Map.keys)

  env = (set _letBindings bindings <<< set _deposits deposits) mempty

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
  lintContract env c1
  lintContract env c2
  case sa of
    (ConstantSimp _ _ c) ->
      if c then do
        addWarning UnreachableContract c2 (getPosition c2)
        pure unit
      else do
        addWarning UnreachableContract c1 (getPosition c1)
        pure unit
    _ -> do
      markSimplification constToObs SimplifiableObservation obs sa
      pure unit

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

lintValue env t@(Term (ChoiceValue choiceId a) pos) = do
  modifying _holes (getHoles choiceId)
  sa <- lintValue env a
  markSimplification constToVal SimplifiableValue a sa
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
  | NoEffect

lintCase :: LintEnv -> Term Case -> CMS.State State Unit
lintCase env t@(Term (Case action contract) pos) = do
  effect <- lintAction env action
  let
    newEnv = case effect of
      ConstantDeposit accTerm tokenTerm amount -> addMoneyToEnvAccount amount accTerm tokenTerm env
      UnknownDeposit accTerm tokenTerm -> over _deposits (Map.insert (accTerm /\ tokenTerm) Nothing) env
      NoEffect -> env
  lintContract newEnv contract
  pure unit

lintCase env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure unit

lintAction :: LintEnv -> Term Action -> CMS.State State Effect
lintAction env t@(Term (Deposit acc party token value) pos) = do
  let
    accTerm = maybe NoEffect (maybe (const NoEffect) UnknownDeposit (fromTerm acc)) (fromTerm token)

    gatherHoles = getHoles acc <> getHoles party <> getHoles token
  modifying _holes (gatherHoles)
  sa <- lintValue env value
  case sa of
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
  modifying _holes (getHoles choiceId <> getHoles bounds)
  when (Array.null bounds) $ addWarning UnreachableCaseEmptyChoice t pos
  pure NoEffect

lintAction env t@(Term (Notify obs) pos) = do
  sa <- lintObservation env obs
  case sa of
    (ConstantSimp _ _ c)
      | not c -> addWarning UnreachableCaseFalseNotify t pos
    _ -> markSimplification constToObs SimplifiableObservation obs sa
  pure NoEffect

lintAction env hole@(Hole _ _ _) = do
  modifying _holes (insertHole hole)
  pure NoEffect

suggestions :: Boolean -> String -> IRange -> Array CompletionItem
suggestions stripParens contract range =
  fromMaybe [] do
    parsedContract <- hush $ parseContract contract
    let
      (Holes holes) = view _holes ((lint (emptyState zero)) parsedContract)
    v <- Map.lookup "monaco_suggestions" holes
    { head } <- Array.uncons $ Set.toUnfoldable v
    pure $ holeSuggestions stripParens range head

-- FIXME: We have multiple model markers, 1 per quick fix. This is wrong though, we need only 1 but in MarloweCodeActionProvider we want to run the code
-- to generate the quick fixes from this single model marker
markers :: Semantics.State -> String -> Array IMarkerData
markers contractState contract = case (lint contractState) <$> parseContract contract of
  Left EmptyInput -> []
  Left e@(ContractParseError { message, row, column, token }) ->
    let
      whiteSpaceChar c = Set.member c $ Set.fromFoldable $ map codePointFromChar [ '\n', '\r', ' ', '\t' ]

      word = takeWhile (not <<< whiteSpaceChar) token
    in
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
  Right state ->
    let
      holesMarkers = state ^. (_holes <<< to holesToMarkers)

      warningsMarkers = state ^. (_warnings <<< to Set.toUnfoldable <<< to (map warningToMarker))
    in
      holesMarkers <> warningsMarkers

-- other types of warning could do with being refactored to a Warning ADT first so we don't need to repeat ourselves
holesToMarkers :: Holes -> Array IMarkerData
holesToMarkers (Holes holes) =
  let
    (allHoles :: Array _) = Set.toUnfoldable $ fold $ Map.values holes
  in
    foldMap holeToMarkers allHoles

holeToMarker :: MarloweHole -> Map String (Array Argument) -> String -> IMarkerData
holeToMarker hole@(MarloweHole { name, marloweType, row, column }) m constructorName =
  { startColumn: column
  , startLineNumber: row
  , endColumn: column + (length name) + 1
  , endLineNumber: row
  , message: holeText marloweType
  , severity: markerSeverity "Warning"
  , code: ""
  , source: "Hole: " <> (dropEnd 4 $ show marloweType)
  }
  where
  dropEnd :: Int -> String -> String
  dropEnd n = fromCodePointArray <<< Array.dropEnd n <<< toCodePointArray

holeToMarkers :: MarloweHole -> Array IMarkerData
holeToMarkers hole@(MarloweHole { name, marloweType, row, column }) =
  let
    m = getMarloweConstructors marloweType

    constructors = take 1 $ Set.toUnfoldable $ Map.keys m
  in
    map (holeToMarker hole m) constructors

markerToHole :: IMarkerData -> MarloweType -> MarloweHole
markerToHole { startColumn, startLineNumber } marloweType = MarloweHole { name: "unknown", marloweType, row: startLineNumber, column: startColumn }

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
    , source: ""
    }

format :: String -> String
format contractString = case parseContract contractString of
  Left _ -> contractString
  Right contract -> show $ pretty contract

provideCodeActions :: Uri -> Array IMarkerData -> Array CodeAction
provideCodeActions uri markers' =
  (flip foldMap) markers' \(marker@{ source, startLineNumber, startColumn, endLineNumber, endColumn }) -> case regex "Hole: (\\w+)" noFlags of
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
