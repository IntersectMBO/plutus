module Data.Symbolic where

import Prelude
import Data.Array ((:))
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)

data Tree a
  = Leaf a
  | Node Constraint Constraint (Tree a) (Tree a)

derive instance genericTree :: Generic (Tree a) _

instance showTree :: Show a => Show (Tree a) where
  show t = genericShow t

derive instance functorTree :: Functor Tree

instance applyTree :: Apply Tree where
  apply (Leaf f) (Leaf a) = Leaf (f a)
  apply lf@(Leaf _) (Node lc rc l r) = Node lc rc (apply lf l) (apply lf r)
  apply (Node lc rc lf rf) la@(Leaf _) = Node lc rc (apply lf la) (apply rf la)
  apply (Node lc rc lf rf) (Node lc' rc' l r) =
    Node lc rc
      (Node lc' rc' (apply lf l) (apply lf r))
      (Node lc' rc' (apply rf l) (apply rf r))

instance applicativeTree :: Applicative Tree where
  pure a = Leaf a

instance bindTree :: Bind Tree where
  bind (Node lc rc l r) f = Node lc rc (bind l f) (bind r f)
  bind (Leaf a) f = f a

instance monadTree :: Monad Tree

instance semigroupTree :: Semigroup (Tree a) where
  append a b = Node STrue STrue a b

type Equation a
  = { constraints :: Array Constraint
    , value :: a
    }

newtype Var
  = Var Int

derive instance genericVar :: Generic Var _

instance showVar :: Show Var where
  show c = genericShow c

derive instance eqVar :: Eq Var

derive instance ordVar :: Ord Var

data StringConstraint
  = StringVar Var
  | StringConst String

derive instance genericStringConstraint :: Generic StringConstraint _

instance showStringConstraint :: Show StringConstraint where
  show c = genericShow c

derive instance eqStringConstraint :: Eq StringConstraint

derive instance ordStringConstraint :: Ord StringConstraint

data IntConstraint
  = IntVar Var
  | IntConst BigInteger
  | IntAdd IntConstraint IntConstraint
  | IntMul IntConstraint IntConstraint
  | IntSub IntConstraint IntConstraint
  | IntEQ IntConstraint IntConstraint
  | IntLT IntConstraint IntConstraint
  | IntLTE IntConstraint IntConstraint
  | IntGT IntConstraint IntConstraint
  | IntGTE IntConstraint IntConstraint

derive instance genericIntConstraint :: Generic IntConstraint _

instance showIntConstraint :: Show IntConstraint where
  show c = genericShow c

derive instance eqIntConstraint :: Eq IntConstraint

derive instance ordIntConstraint :: Ord IntConstraint

instance semiringIntConstraint :: Semiring IntConstraint where
  zero = IntConst zero
  one = IntConst one
  add = IntAdd
  mul = IntMul

instance ringIntConstraint :: Ring IntConstraint where
  sub = IntSub

infixr 5 IntLT as .<

infixr 5 IntLTE as .<=

infixr 5 IntGT as .>

infixr 5 IntGTE as .>=

data Constraint
  = STrue
  | SNot Constraint
  | SAnd Constraint Constraint
  | SOr Constraint Constraint
  | SInt IntConstraint
  | SString StringConstraint

derive instance genericConstraint :: Generic Constraint _

instance showConstraint :: Show Constraint where
  show c = genericShow c

-- | Symbolic version of if constraint then t else f
ite :: forall a. Constraint -> Tree a -> Tree a -> Tree a
ite constraint t f =
  let
    leftConstraint = constraint

    rightConstraint = SNot constraint
  in
    Node leftConstraint rightConstraint t f

is :: Constraint -> Tree Boolean
is const = Node const (SNot const) (pure true) (pure false)

and :: Constraint -> Constraint -> Tree Boolean
and a b = is (SAnd a b)

infixr 5 and as .&&

or :: Constraint -> Constraint -> Tree Boolean
or a b = is (SOr a b)

infixr 5 or as .||

smin :: IntConstraint -> IntConstraint -> Tree IntConstraint
smin a b = ite (SInt (a .< b)) (pure a) (pure b)

-- | A node contains the constraint to go in either branch.
--   We traverse the tree collecting the constraints as we go until we get to a leaf
--   For every leaf we will return a value and all the constraints required to get there
--   TODO: The constraints are probably a mess that can be simplified
getEquations :: forall a. Tree a -> Array (Equation a)
getEquations t = go mempty mempty t
  where
  go equations constraints (Leaf a) = { constraints: constraints, value: a } : equations

  go equations constraints (Node lc rc l r) =
    let
      leftEquations = go equations (lc : constraints) l

      rightEquations = go equations (rc : constraints) r
    in
      leftEquations <> rightEquations
