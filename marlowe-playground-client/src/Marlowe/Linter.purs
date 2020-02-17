module Marlowe.Linter
  ( lint
  , State(..)
  , Position
  , MaxTimeout
  , _holes
  , _negativeDeposits
  , _negativePayments
  , _timeoutNotIncreasing
  , _uninitializedUse
  , _shadowedLet
  , _trueObservation
  , _falseObservation
  ) where

import Prelude
import Data.Array (catMaybes, cons, fold, foldMap, (:))
import Data.BigInteger (BigInteger)
import Data.Lens (Lens', over, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Holes (Action(..), Case(..), Contract(..), Holes, Observation(..), Term(..), Value(..), ValueId, getHoles, insertHole)
import Marlowe.Semantics (Timeout)
import Text.Parsing.StringParser (Pos)

type Position
  = { start :: Pos, end :: Pos }

newtype MaxTimeout
  = MaxTimeout Timeout

derive instance newtypeMaxTimeout :: Newtype MaxTimeout _

derive newtype instance eqMaxTimeout :: Eq MaxTimeout

derive newtype instance ordMaxTimeout :: Ord MaxTimeout

instance semigroupMax :: Semigroup MaxTimeout where
  append a b = max a b

instance monoidMaxTimeout :: Monoid MaxTimeout where
  mempty = MaxTimeout zero

newtype State
  = State
  { holes :: Holes
  , negativePayments :: Array Position
  , negativeDeposits :: Array Position
  , maxTimeout :: MaxTimeout
  , timeoutNotIncreasing :: Array Position
  , letBindings :: Set ValueId
  , uninitializedUse :: Array Position
  , shadowedLet :: Array Position
  , trueObservation :: Array Position
  , falseObservation :: Array Position
  }

derive instance newtypeState :: Newtype State _

derive newtype instance semigroupState :: Semigroup State

derive newtype instance monoidState :: Monoid State

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_negativePayments :: Lens' State (Array Position)
_negativePayments = _Newtype <<< prop (SProxy :: SProxy "negativePayments")

_negativeDeposits :: Lens' State (Array Position)
_negativeDeposits = _Newtype <<< prop (SProxy :: SProxy "negativeDeposits")

_maxTimeout :: Lens' State Timeout
_maxTimeout = _Newtype <<< prop (SProxy :: SProxy "maxTimeout") <<< _Newtype

_timeoutNotIncreasing :: Lens' State (Array Position)
_timeoutNotIncreasing = _Newtype <<< prop (SProxy :: SProxy "timeoutNotIncreasing")

_letBindings :: Lens' State (Set ValueId)
_letBindings = _Newtype <<< prop (SProxy :: SProxy "letBindings")

_uninitializedUse :: Lens' State (Array Position)
_uninitializedUse = _Newtype <<< prop (SProxy :: SProxy "uninitializedUse")

_shadowedLet :: Lens' State (Array Position)
_shadowedLet = _Newtype <<< prop (SProxy :: SProxy "shadowedLet")

_trueObservation :: Lens' State (Array Position)
_trueObservation = _Newtype <<< prop (SProxy :: SProxy "trueObservation")

_falseObservation :: Lens' State (Array Position)
_falseObservation = _Newtype <<< prop (SProxy :: SProxy "falseObservation")

-- | We go through a contract term collecting all warnings and holes etc so that we can display them in the editor
-- | The aim here is to only traverse the contract once since we are concerned about performance with the linting
lint :: Term Contract -> State
lint = go mempty
  where
  go :: State -> Term Contract -> State
  go state (Term Close _ _) = state

  go state (Term (Pay acc payee token payment contract) start end) =
    let
      gatherHoles = getHoles acc <> getHoles payee <> getHoles token

      newState =
        state
          # over _holes gatherHoles
          # over _negativePayments (maybeCons (negativeValue payment))
    in
      go newState contract <> lintValue newState payment

  go state (Term (If obs c1 c2) _ _) = go state c1 <> go state c2 <> lintObservation state obs

  go state (Term (When cases timeoutTerm contract) _ _) =
    let
      (states /\ contracts) = collectFromTuples (map (lintCase state) cases)

      newState = case timeoutTerm of
        (Term timeout start end) ->
          let
            timeoutNotIncreasing = if timeout > (view _maxTimeout state) then [] else [ { start, end } ]
          in
            (fold states)
              # over _holes (insertHole timeoutTerm)
              # over _maxTimeout (max timeout)
              # over _timeoutNotIncreasing (append timeoutNotIncreasing)
        _ ->
          (fold states)
            # over _holes (insertHole timeoutTerm)
    in
      foldMap (go newState) (contract : catMaybes contracts)

  go state (Term (Let valueIdTerm value contract) _ _) =
    let
      gatherHoles = getHoles valueIdTerm

      newState = case valueIdTerm of
        (Term valueId start end) ->
          let
            shadowedLet = if Set.member valueId (view _letBindings state) then [ { start, end } ] else []
          in
            state
              # over _holes gatherHoles
              # over _negativePayments (maybeCons (negativeValue value))
              # over _letBindings (Set.insert valueId)
              # over _shadowedLet (append shadowedLet)
        _ ->
          state
            # over _holes gatherHoles
            # over _negativePayments (maybeCons (negativeValue value))
    in
      go newState contract <> lintValue newState value

  go state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state

lintObservation :: State -> Term Observation -> State
lintObservation state (Term (AndObs a b) _ _) = lintObservation state a <> lintObservation state b

lintObservation state (Term (OrObs a b) _ _) = lintObservation state a <> lintObservation state b

lintObservation state (Term (NotObs a) _ _) = lintObservation state a

lintObservation state (Term (ChoseSomething choiceId) _ _) = over _holes (getHoles choiceId) state

lintObservation state (Term (ValueGE a b) _ _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueGT a b) _ _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueLT a b) _ _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueLE a b) _ _) = lintValue state a <> lintValue state b

lintObservation state (Term (ValueEQ a b) _ _) = lintValue state a <> lintValue state b

lintObservation state (Term TrueObs start end) = over _trueObservation (cons { start, end }) state

lintObservation state (Term FalseObs start end) = over _falseObservation (cons { start, end }) state

lintObservation state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state

lintValue :: State -> Term Value -> State
lintValue state (Term (AvailableMoney acc token) _ _) =
  let
    gatherHoles = getHoles acc <> getHoles token
  in
    over _holes (gatherHoles) state

lintValue state (Term (Constant a) _ _) = over _holes (insertHole a) state

lintValue state (Term (NegValue a) _ _) = lintValue state a

lintValue state (Term (AddValue a b) _ _) = lintValue state a <> lintValue state b

lintValue state (Term (SubValue a b) _ _) = lintValue state a <> lintValue state b

lintValue state (Term (ChoiceValue choiceId a) _ _) =
  let
    newState = over _holes (getHoles choiceId) state
  in
    lintValue newState a

lintValue state (Term SlotIntervalStart _ _) = state

lintValue state (Term SlotIntervalEnd _ _) = state

lintValue state (Term (UseValue (Term valueId start end)) _ _) =
  let
    uninitializedUse = if Set.member valueId (view _letBindings state) then [] else [ { start, end } ]
  in
    state
      # over _holes (getHoles valueId)
      # over _uninitializedUse (append uninitializedUse)

lintValue state (Term (UseValue hole) _ _) = over _holes (insertHole hole) state

lintValue state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state

maybeCons :: forall a. Maybe a -> Array a -> Array a
maybeCons Nothing xs = xs

maybeCons (Just x) xs = x : xs

collectFromTuples :: forall a b. Array (a /\ b) -> Array a /\ Array b
collectFromTuples = foldMap (\(a /\ b) -> [ a ] /\ [ b ])

lintCase :: State -> Term Case -> State /\ Maybe (Term Contract)
lintCase state (Term (Case action contract) _ _) =
  let
    newState =
      state
        # over _negativeDeposits (maybeCons (negativeDeposit action))
  in
    lintAction newState action /\ Just contract

lintCase state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state /\ Nothing

lintAction :: State -> Term Action -> State
lintAction state (Term (Deposit acc party token value) _ _) =
  let
    gatherHoles = getHoles acc <> getHoles party <> getHoles token

    newState = over _holes (gatherHoles) state
  in
    lintValue newState value

lintAction state (Term (Choice choiceId bounds) _ _) = over _holes (getHoles choiceId <> getHoles bounds) state

lintAction state (Term (Notify obs) _ _) = lintObservation state obs

lintAction state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state

negativeDeposit :: Term Action -> Maybe Position
negativeDeposit (Term (Deposit _ _ _ value) _ _) = negativeValue value

negativeDeposit _ = Nothing

negativeValue :: Term Value -> Maybe Position
negativeValue term@(Term _ start end) = case constantValue term of
  Nothing -> Nothing
  Just v -> if v < zero then Just { start, end } else Nothing

negativeValue _ = Nothing

constantValue :: Term Value -> Maybe BigInteger
constantValue (Term (Constant (Term v _ _)) _ _) = Just v

constantValue (Term (NegValue v) _ _) = negate <$> constantValue v

constantValue (Term (AddValue a b) _ _) = do
  va <- constantValue a
  vb <- constantValue b
  pure (va + vb)

constantValue (Term (SubValue a b) _ _) = do
  va <- constantValue a
  vb <- constantValue b
  pure (va - vb)

constantValue _ = Nothing
