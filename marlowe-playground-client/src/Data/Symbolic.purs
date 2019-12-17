module Data.Symbolic where

import Prelude
import Data.Array (fold, foldMap, (:))
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Set (Set)
import Data.Set as Set
import Data.String (joinWith)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Z3.Monad (Z3, evalString)

data Tree a
  = Leaf a
  | Node BooleanConstraint BooleanConstraint (Tree a) (Tree a)

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
  append a b = Node True True a b

type Equation a
  = { constraints :: Array BooleanConstraint
    , value :: a
    }

data SExp
  = Atom String
  | Exp String (Array SExp)

derive instance eqSExp :: Eq SExp

derive instance ordSExp :: Ord SExp

class ToSExp a where
  toSexp :: a -> SExp

instance showSExp :: Show SExp where
  show (Atom x) = x
  show (Exp name args) = "(" <> name <> foldMap (\v -> " " <> show v) args <> ")"

data Sort
  = StringSort
  | IntSort

derive instance genericSort :: Generic Sort _

instance showSort :: Show Sort where
  show StringSort = "String"
  show IntSort = "Int"

derive instance eqSort :: Eq Sort

derive instance ordSort :: Ord Sort

data Var
  = Var String Sort

derive instance genericVar :: Generic Var _

instance showVar :: Show Var where
  show c = genericShow c

derive instance eqVar :: Eq Var

derive instance ordVar :: Ord Var

instance toSexpVar :: ToSExp Var where
  toSexp (Var x _) = Atom x

data StringConstraint
  = StringVar Var
  | StringConst String
  | StringEQ StringConstraint StringConstraint

derive instance genericStringConstraint :: Generic StringConstraint _

instance showStringConstraint :: Show StringConstraint where
  show c = genericShow c

derive instance eqStringConstraint :: Eq StringConstraint

derive instance ordStringConstraint :: Ord StringConstraint

instance sexpStringConstraint :: ToSExp StringConstraint where
  toSexp (StringVar v) = toSexp v
  toSexp (StringConst x) = Atom x
  toSexp (StringEQ a b) = Exp "=" $ map toSexp [ a, b ]

stringVar :: String -> StringConstraint
stringVar name = StringVar $ Var name StringSort

data IntConstraint
  = IntVar Var
  | IntConst BigInteger
  | IntAdd IntConstraint IntConstraint
  | IntMul IntConstraint IntConstraint
  | IntSub IntConstraint IntConstraint

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

intVar :: String -> IntConstraint
intVar name = IntVar $ Var name IntSort

data BooleanConstraint
  = True
  | Not BooleanConstraint
  | And BooleanConstraint BooleanConstraint
  | Or BooleanConstraint BooleanConstraint
  | BooleanEQ BooleanConstraint BooleanConstraint
  | IntEQ IntConstraint IntConstraint
  | IntLT IntConstraint IntConstraint
  | IntLTE IntConstraint IntConstraint
  | IntGT IntConstraint IntConstraint
  | IntGTE IntConstraint IntConstraint

derive instance genericBooleanConstraint :: Generic BooleanConstraint _

instance showBooleanConstraint :: Show BooleanConstraint where
  show c = genericShow c

derive instance eqBooleanConstraint :: Eq BooleanConstraint

derive instance ordBooleanConstraint :: Ord BooleanConstraint

instance semigroupBooleanConstraint :: Semigroup BooleanConstraint where
  append a b = And a b

instance sexpBooleanConstraint :: ToSExp BooleanConstraint where
  toSexp True = Atom "true"
  toSexp (Not a) = Exp "not" $ [ toSexp a ]
  toSexp (And a b) = Exp "and" $ map toSexp [ a, b ]
  toSexp (Or a b) = Exp "or" $ map toSexp [ a, b ]
  toSexp (BooleanEQ a b) = Exp "=" $ map toSexp [ a, b ]
  toSexp (IntEQ a b) = Exp "=" $ map toSexp [ a, b ]
  toSexp (IntLT a b) = Exp "<" $ map toSexp [ a, b ]
  toSexp (IntLTE a b) = Exp "<=" $ map toSexp [ a, b ]
  toSexp (IntGT a b) = Exp ">" $ map toSexp [ a, b ]
  toSexp (IntGTE a b) = Exp ">=" $ map toSexp [ a, b ]

infixr 5 IntLT as .<

infixr 5 IntLTE as .<=

infixr 5 IntGT as .>

infixr 5 IntGTE as .>=

data Constraint
  = SBoolean BooleanConstraint
  | SInt IntConstraint
  | SString StringConstraint
  | SEq Constraint Constraint

derive instance genericConstraint :: Generic Constraint _

instance showConstraint :: Show Constraint where
  show c = genericShow c

instance sexpConstraint :: ToSExp Constraint where
  toSexp (SBoolean a) = toSexp a
  toSexp (SInt a) = toSexp a
  toSexp (SString a) = toSexp a
  toSexp (SEq a b) = Exp "=" (map toSexp [ a, b ])

-- | Symbolic version of if constraint then t else f
ite :: forall a. BooleanConstraint -> Tree a -> Tree a -> Tree a
ite constraint t f =
  let
    leftConstraint = constraint

    rightConstraint = Not constraint
  in
    Node leftConstraint rightConstraint t f

is :: BooleanConstraint -> Tree Boolean
is c = Node c (Not c) (pure true) (pure false)

and :: BooleanConstraint -> BooleanConstraint -> Tree Boolean
and a b = is (And a b)

infixr 5 and as .&&

or :: BooleanConstraint -> BooleanConstraint -> Tree Boolean
or a b = is (Or a b)

infixr 5 or as .||

smin :: IntConstraint -> IntConstraint -> Tree IntConstraint
smin a b = ite (a .< b) (pure a) (pure b)

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

assertion :: BooleanConstraint -> SExp
assertion constraint = Exp "assert" [ toSexp constraint ]

assertions :: forall a. Equation a -> Set SExp
assertions { constraints } = Set.fromFoldable $ map assertion constraints

intVariable :: IntConstraint -> Array Var
intVariable (IntVar var) = [ var ]

intVariable (IntConst _) = []

intVariable (IntAdd a b) = intVariable a <> intVariable b

intVariable (IntMul a b) = intVariable a <> intVariable b

intVariable (IntSub a b) = intVariable a <> intVariable b

booleanVariable :: BooleanConstraint -> Array Var
booleanVariable True = []

booleanVariable (Not a) = booleanVariable a

booleanVariable (And a b) = booleanVariable a <> booleanVariable b

booleanVariable (Or a b) = booleanVariable a <> booleanVariable b

booleanVariable (BooleanEQ a b) = booleanVariable a <> booleanVariable b

booleanVariable (IntEQ a b) = intVariable a <> intVariable b

booleanVariable (IntLT a b) = intVariable a <> intVariable b

booleanVariable (IntLTE a b) = intVariable a <> intVariable b

booleanVariable (IntGT a b) = intVariable a <> intVariable b

booleanVariable (IntGTE a b) = intVariable a <> intVariable b

stringVariable :: StringConstraint -> Array Var
stringVariable (StringVar var) = [ var ]

stringVariable _ = []

variable :: Constraint -> Array Var
variable (SInt x) = intVariable x

variable (SString s) = stringVariable s

variable (SBoolean b) = booleanVariable b

variable (SEq a b) = variable a <> variable b

variables :: forall a. Equation a -> Set Var
variables { constraints } = Set.fromFoldable $ fold $ map booleanVariable constraints

declareConst :: Var -> SExp
declareConst (Var name sort) = Exp "declare-const" [ Atom name, Atom (show sort) ]

checkSat :: SExp
checkSat = Exp "check-sat" []

getModel :: SExp
getModel = Exp "get-model" []

getValue :: Var -> SExp
getValue (Var v _) = Exp "get-value" $ [ Exp v [] ]

equationModel :: forall a. Equation a -> Z3 (Array (Tuple String String))
equationModel e = traverse f $ Set.toUnfoldable $ variables e
  where
  f :: Var -> Z3 (Tuple String String)
  f v@(Var name _) = do
    let
      exp = getValue v
    res <- evalString $ show exp
    pure (Tuple name res)

solveEquation :: forall a. Equation a -> Z3 String
solveEquation e =
  let
    vs = joinWith "\n" $ Set.toUnfoldable $ Set.map (show <<< declareConst) $ variables e

    as = joinWith "\n" $ map show $ Set.toUnfoldable $ assertions e

    s = vs <> "\n" <> as
  in
    evalString s
