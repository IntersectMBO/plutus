module Marlowe.Linter
  ( lint
  , State(..)
  , Position
  , _holes
  , _negativeDeposits
  , _negativePayments
  ) where

import Prelude
import Data.Array (catMaybes, fold, foldMap, (:))
import Data.BigInteger (BigInteger)
import Data.Lens (Lens', over, set, view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Holes (Action(..), Case(..), Contract(..), Holes, Term(..), Value(..), getHoles, insertHole)
import Text.Parsing.StringParser (Pos)

type Position
  = { start :: Pos, end :: Pos }

newtype State
  = State
  { holes :: Holes
  , negativePayments :: Array Position
  , negativeDeposits :: Array Position
  }

derive instance newtypeState :: Newtype State _

instance semigroupState :: Semigroup State where
  append (State s1) (State s2) =
    State
      { holes: s1.holes <> s2.holes
      , negativePayments: s1.negativePayments <> s2.negativePayments
      , negativeDeposits: s1.negativeDeposits <> s2.negativeDeposits
      }

instance monoidState :: Monoid State where
  mempty =
    State
      { holes: mempty
      , negativePayments: mempty
      , negativeDeposits: mempty
      }

_holes :: Lens' State Holes
_holes = _Newtype <<< prop (SProxy :: SProxy "holes")

_negativePayments :: Lens' State (Array Position)
_negativePayments = _Newtype <<< prop (SProxy :: SProxy "negativePayments")

_negativeDeposits :: Lens' State (Array Position)
_negativeDeposits = _Newtype <<< prop (SProxy :: SProxy "negativeDeposits")

lint :: Term Contract -> State
lint = traverseContract mempty

-- | We go through a contract term collecting all warnings and holes etc so that we can display them in the editor
traverseContract :: State -> Term Contract -> State
traverseContract state (Term Close _ _) = state

traverseContract state (Term (Pay acc payee token payment contract) start end) =
  let
    gatherHoles = getHoles acc <> getHoles payee <> getHoles token <> getHoles payment

    newState =
      over _holes gatherHoles
        <<< over _negativePayments (maybeCons (negativeValue payment))
        $ state
  in
    traverseContract newState contract

traverseContract state (Term (If obs c1 c2) _ _) =
  let
    gatherHoles = getHoles obs

    newState = over _holes gatherHoles state
  in
    traverseContract newState c1 <> traverseContract newState c2

traverseContract state (Term (When cases timeout contract) start end) =
  let
    hs = view _holes state

    (holes /\ mnds /\ contracts) = collectFromTuples (map (contractFromCase hs) cases)

    nds = catMaybes mnds

    newState =
      over _negativeDeposits (append nds)
        <<< set _holes (insertHole timeout (fold holes))
        $ state
  in
    fold $ map (traverseContract newState) (contract : catMaybes contracts)

traverseContract state (Term (Let valueId value contract) _ _) =
  let
    gatherHoles = getHoles valueId <> getHoles value

    newState =
      over _holes gatherHoles
        <<< over _negativePayments (maybeCons (negativeValue value))
        $ state
  in
    traverseContract newState contract

traverseContract state hole@(Hole _ _ _ _) = over _holes (insertHole hole) state

maybeCons :: forall a. Maybe a -> Array a -> Array a
maybeCons Nothing xs = xs

maybeCons (Just x) xs = x : xs

collectFromTuples :: forall a b c. Array (a /\ b /\ c) -> Array a /\ Array b /\ Array c
collectFromTuples = foldMap (\(a /\ b /\ c) -> [ a ] /\ [ b ] /\ [ c ])

contractFromCase :: Holes -> Term Case -> Holes /\ Maybe Position /\ Maybe (Term Contract)
contractFromCase holes (Term (Case action contract) _ _) = getHoles action holes /\ negativeDeposit action /\ Just contract

contractFromCase holes _ = holes /\ Nothing /\ Nothing

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
