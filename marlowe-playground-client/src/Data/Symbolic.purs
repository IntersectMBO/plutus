module Data.Symbolic where

import Prelude
import Control.Alt ((<|>))
import Data.Array (fold, foldMap, intercalate, (:))
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

data SExp
  = Atom String
  | Exp String (Array SExp)

class ToSExp a where
  toSexp :: a -> SExp

instance showSExp :: Show SExp where
  show (Atom x) = x
  show (Exp name args) = "(" <> name <> foldMap (\v -> " " <> show v) args <> ")"

newtype Var
  = Var String

derive instance genericVar :: Generic Var _

instance showVar :: Show Var where
  show c = genericShow c

derive instance eqVar :: Eq Var

derive instance ordVar :: Ord Var

instance toSexpVar :: ToSExp Var where
  toSexp (Var x) = Atom x

data StringConstraint
  = StringVar Var
  | StringConst String

derive instance genericStringConstraint :: Generic StringConstraint _

instance showStringConstraint :: Show StringConstraint where
  show c = genericShow c

derive instance eqStringConstraint :: Eq StringConstraint

derive instance ordStringConstraint :: Ord StringConstraint

instance sexpStringConstraint :: ToSExp StringConstraint where
  toSexp (StringVar v) = toSexp v
  toSexp (StringConst x) = Atom x

stringVar :: String -> StringConstraint
stringVar = StringVar <<< Var

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

instance sexpIntConstraint :: ToSExp IntConstraint where
  toSexp (IntVar v) = toSexp v
  toSexp (IntConst x) = Atom $ show x
  toSexp (IntAdd a b) = Exp "+" $ map toSexp [ a, b ]
  toSexp (IntMul a b) = Exp "*" $ map toSexp [ a, b ]
  toSexp (IntSub a b) = Exp "-" $ map toSexp [ a, b ]
  toSexp (IntEQ a b) = Exp "=" $ map toSexp [ a, b ]
  toSexp (IntLT a b) = Exp "<" $ map toSexp [ a, b ]
  toSexp (IntLTE a b) = Exp "<=" $ map toSexp [ a, b ]
  toSexp (IntGT a b) = Exp ">" $ map toSexp [ a, b ]
  toSexp (IntGTE a b) = Exp ">=" $ map toSexp [ a, b ]

intVar :: String -> IntConstraint
intVar = IntVar <<< Var

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
  | SEq Constraint Constraint

derive instance genericConstraint :: Generic Constraint _

instance showConstraint :: Show Constraint where
  show c = genericShow c

instance sexpConstraint :: ToSExp Constraint where
  toSexp STrue = Atom "true"
  toSexp (SNot a) = Exp "not" [ toSexp a ]
  toSexp (SAnd a b) = Exp "and" (map toSexp [ a, b ])
  toSexp (SOr a b) = Exp "or" (map toSexp [ a, b ])
  toSexp (SInt a) = toSexp a
  toSexp (SString a) = toSexp a
  toSexp (SEq a b) = Exp "=" (map toSexp [ a, b ])

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

assertion :: Constraint -> SExp
assertion constraint = Exp "assert" [ toSexp constraint ]

assertions :: forall a. Equation a -> Array SExp
assertions { constraints } = map assertion constraints

intVariable :: IntConstraint -> Array SExp
intVariable (IntVar (Var name)) = [ Exp "declare-const" [ Atom name, Atom "Int" ] ]

intVariable (IntConst _) = []

intVariable (IntAdd a b) = intVariable a <> intVariable b

intVariable (IntMul a b) = intVariable a <> intVariable b

intVariable (IntSub a b) = intVariable a <> intVariable b

intVariable (IntEQ a b) = intVariable a <> intVariable b

intVariable (IntLT a b) = intVariable a <> intVariable b

intVariable (IntLTE a b) = intVariable a <> intVariable b

intVariable (IntGT a b) = intVariable a <> intVariable b

intVariable (IntGTE a b) = intVariable a <> intVariable b

stringVariable :: StringConstraint -> Array SExp
stringVariable (StringVar (Var name)) = [ Exp "declare-const" [ Atom name, Atom "String" ] ]

stringVariable _ = []

variable :: Constraint -> Array SExp
variable (SInt x) = intVariable x

variable (SString s) = stringVariable s

variable STrue = []

variable (SNot a) = variable a

variable (SAnd a b) = variable a <|> variable b

variable (SOr a b) = variable a <|> variable b

variable (SEq a b) = variable a <|> variable b

variables :: forall a. Equation a -> Array SExp
variables { constraints } = fold $ map variable constraints

checkSat :: SExp
checkSat = Exp "check-sat" []

getModel :: SExp
getModel = Exp "get-model" []

toZ3 :: forall a. Equation a -> String
toZ3 e = intercalate "\n" $ map show $ variables e <> assertions e <> [ checkSat, getModel ]
