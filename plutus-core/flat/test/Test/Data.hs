{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-
 A collection of data types used for testing.
-}
module Test.Data where

import Data.Data
import Data.Int
import Data.Word
import GHC.Generics
import Test.Data2 qualified as D2

-- import           Test.Tasty.QuickCheck
data Void
  deriving (Generic)

data X = X X
  deriving (Generic)

data Unit = Unit
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Un = Un {un :: Bool}
  deriving (Eq, Ord, Read, Show, Data, Generic)

data D2 = D2 Bool N
  deriving (Eq, Ord, Read, Show, Data, Generic)

data D4 = D4 Bool N Unit N3
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- Enumeration
data N3
  = N1
  | N2
  | N3
  deriving (Eq, Ord, Read, Show, Data, Generic, Enum)

data N
  = One
  | Two
  | Three
  | Four
  | Five
  deriving (Eq, Ord, Read, Show, Data, Generic, Enum, Bounded)

-- toForestD :: Forest a -> ForestD (Tr2 a)
-- toForestD (Forest lt) = undefined -- Forest2 (ForestD (map (\t -> let Tr2 tt = treeConv t in tt) . toList $ lt))
-- toForestD (Forest lt) = undefined -- Forest2 (ForestD (map (\t -> let Tr2 tt = treeConv t in tt) . toList $ lt))
toForest2 :: Forest a -> Forest2 a
toForest2 (Forest f) = Forest2 (ForestD $ fmap toTr f)

toTr :: Tr a -> TrD (Forest2 a) a
toTr (Tr a f) = TrD a (toForest2 f)

toTr2 :: Tr a -> Tr2 a
toTr2 (Tr a (Forest f)) = Tr2 (TrD a (ForestD $ fmap toTr2 f))

-- tying the recursive knot, equivalent to Forest/Tree
data Forest2 a = Forest2 (ForestD (TrD (Forest2 a) a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Tr2 a = Tr2 (TrD (ForestD (Tr2 a)) a)
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- First-order non mutually recursive
data ForestD t = ForestD (List t)
  deriving (Eq, Ord, Read, Show, Data, Generic)

data TrD f a = TrD a f
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- Explicit mutually recursive
data Forest a = Forest (List (Tr a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Tr a = Tr a (Forest a)
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Words = Words Word8 Word16 Word32 Word64
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Ints = Ints Int8 Int16 Int32 Int64
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- non-recursive data type
data Various
  = V1 (Maybe Bool)
  | -- | V2 Bool (Either Bool (Maybe Bool)) (N,N,N)
    V2 Bool (Either Bool (Maybe Bool))
  | VF Float Double Double
  | VW Word Word8 Word16 Word32 Word64
  | VI Int Int8 Int16 Int32 Int64
  | VII Integer Integer Integer
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- Phantom type
data Phantom a = Phantom
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- Recursive data types
data RR a b c
  = RN {rna :: a, rnb :: b, rnc :: c}
  | RA a (RR a a c) b
  | RAB a (RR c b a) b
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Expr
  = ValB Bool
  | Or Expr Expr
  | If Expr Expr Expr
  deriving (Eq, Ord, Read, Show, Data, Generic)

data List a
  = C a (List a)
  | N
  deriving
    ( Eq
    , Ord
    , Read
    , Show
    , Traversable
    , Data
    , Generic
    , Generic1
    , Functor
    , Foldable
    )

data ListS a
  = Nil
  | Cons a (ListS a)
  deriving
    ( Eq
    , Ord
    , Read
    , Show
    , Functor
    , Foldable
    , Traversable
    , Data
    , Generic
    , Generic1
    )

-- non-regular Haskell datatypes like:
-- Binary instances but no Model
data Nest a
  = NilN
  | ConsN (a, Nest (a, a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

data TN a
  = LeafT a
  | BranchT (TN (a, a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Bush a
  = NilB
  | ConsB (a, Bush (Bush a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- Perfectly balanced binary tree
data Perfect a
  = ZeroP a
  | SuccP (Perfect (Fork a))
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Fork a = Fork a a
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- non regular with higher-order kind parameters
-- no Binary/Model instances
data PerfectF f α
  = NilP
  | ConsP α (PerfectF f (f α))
  deriving (Generic) -- No Data

data Pr f g a = Pr (f a (g a))

data Higher f a = Higher (f a)
  deriving (Generic, Data)

-- data Pr2 (f :: * -> *) a = Pr2 (f )
data Free f a
  = Pure a
  | Roll (f (Free f a))
  deriving (Generic)

-- mutual references
data A
  = A B
  | AA Int
  deriving (Eq, Ord, Read, Show, Data, Generic)

data B
  = B A
  | BB Char
  deriving (Eq, Ord, Read, Show, Data, Generic)

-- recursive sets:
-- Prob: ghc will just explode on this
-- data MM1 = MM1 MM2 MM4 MM0 deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM0 = MM0 deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM2 = MM2 MM3 Bool deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM3 = MM3 MM4 Bool deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM4 = MM4 MM4 MM2 MM5 deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM5 = MM5 Unit MM6 deriving (Eq, Ord, Read, Show, Data, Generic)
-- data MM6 = MM6 MM5 deriving (Eq, Ord, Read, Show, Data, Generic)
data A0
  = A0 B0 B0 D0 Bool
  | A1 (List Bool) (List Unit) (D2.List Bool) (D2.List Bool)
  deriving (Eq, Ord, Read, Show, Data, Generic)

data B0
  = B0 C0
  | B1
  deriving (Eq, Ord, Read, Show, Data, Generic)

data C0
  = C0 A0
  | C1
  deriving (Eq, Ord, Read, Show, Data, Generic)

data D0
  = D0 E0
  | D1
  deriving (Eq, Ord, Read, Show, Data, Generic)

data E0
  = E0 D0
  | E1
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Even
  = Zero
  | SuccE Odd

data Odd = SuccO Even

-- Existential types
-- data Fold a b = forall x. Fold (x -> a -> x) x (x -> b)
-- data Some :: (* -> *) -> * where
--   Some :: f a -> Some f
-- data Dict (c :: Constraint) where
--   Dict :: c => Dict c
data Direction
  = North
  | South
  | Center
  | East
  | West
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Stream a = Stream a (Stream a)
  deriving
    ( Eq
    , Ord
    , Read
    , Show
    , Data
    , Generic
    , Functor
    , Foldable
    , Traversable
    )

data Tree a
  = Node (Tree a) (Tree a)
  | Leaf a
  deriving (Eq, Ord, Read, Show, Data, Generic, Foldable)

-- Example schema from: http://mechanical-sympathy.blogspot.co.uk/2014/05/simple-binary-encoding.html
data Car
  = Car
  { serialNumber :: Word64
  , modelYear :: Word16
  , available :: Bool
  , code :: CarModel
  , someNumbers :: [Int32]
  , vehicleCode :: String
  , extras :: [OptionalExtra]
  , engine :: Engine
  , fuelFigures :: [Consumption]
  , performanceFigures :: [(OctaneRating, [Acceleration])]
  , make :: String
  , carModel :: String
  }
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Acceleration = Acceleration {mph :: Word16, seconds :: Float}
  deriving (Eq, Ord, Read, Show, Data, Generic)

type OctaneRating = Word8 -- minValue="90" maxValue="110"

data Consumption = Consumption {cSpeed :: Word16, cMpg :: Float}
  deriving (Eq, Ord, Read, Show, Data, Generic)

data CarModel
  = ModelA
  | ModelB
  | ModelC
  deriving (Eq, Ord, Read, Show, Data, Generic)

data OptionalExtra
  = SunRoof
  | SportsPack
  | CruiseControl
  deriving (Eq, Ord, Read, Show, Data, Generic)

data Engine = Engine
  { capacity :: Word16
  , numCylinders :: Word8
  , maxRpm :: Word16 -- constant 9000
  , manufacturerCode :: String
  , fuel :: String -- constant Petrol
  }
  deriving (Eq, Ord, Read, Show, Data, Generic)
