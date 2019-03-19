{-# OPTIONS_GHC
  -fno-warn-missing-signatures -fno-warn-unused-matches -fno-warn-unused-top-binds #-}

module Marlowe
  ( Money(..)
  , Observation(..)
  , Contract(..)
  , Person
  , Random
  , BlockNumber
  , Cash
  , ConcreteChoice
  , Timeout
  , IdentCC(..)
  , IdentChoice(..)
  , IdentPay(..)
  , prettyPrintContract
  ) where

import           Data.List (intercalate)

{-# ANN module "HLint: ignore" #-}

-- Standard library functions
groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _ [] = []
groupBy eq (x:xs) = (x : ys) : groupBy eq zs
  where
    (ys, zs) = span (eq x) xs
  -- People are represented by their public keys,
  -- which in turn are given by integers.

type Key = Int -- Public key

type Person = Key

-- Block numbers and random numbers are both integers.
type Random = Int

type BlockNumber = Int

-- Observables are things which are recorded on the blockchain.
--  e.g. "a random choice", the value of GBP/BTC exchange rate, …
-- Question: how do we implement these things?
--  - We assume that some mechanism exists which will ensure that the value is looked up and recorded, or …
--  - … we actually provide that mechanism explicitly, e.g. with inter-contract comms or transaction generation or something.
-- Other observables are possible, e.g. the value of the oil price at this time.
-- It is assumed that these would be provided in some agreed way by an oracle of some sort.
-- The Observable data type represents the different sorts of observables, …
data Observable
  = Random
  | BlockNumber
  deriving (Eq)

showObservable Random      = "Random"
showObservable BlockNumber = "BlockNumber"

-- Inputs
-- Types for cash commits, money redeems, and choices.
--
-- A cash commitment is an integer (should be positive integer?)
-- Concrete values are sometimes chosen too: these are integers for the sake of this model.
type Cash = Int

type ConcreteChoice = Int

-- We need to put timeouts on various operations. These could be some abstract time
-- domain, but it only really makes sense for these to be block numbers.
type Timeout = BlockNumber

-- Commitments, choices and payments are all identified by identifiers.
-- Their types are given here. In a more sophisticated model these would
-- be generated automatically (and so uniquely); here we simply assume that
-- they are unique.
newtype IdentCC =
  IdentCC Int
  deriving (Eq)

newtype IdentChoice =
  IdentChoice Int
  deriving (Eq)

newtype IdentPay =
  IdentPay Int
  deriving (Eq)

-- Money is a set of contract primitives that represent constants,
-- functions, and variables that can be evaluated as an ammount
-- of money.
data Money
  = AvailableMoney IdentCC
  | AddMoney Money
             Money
  | ConstMoney Cash
  | MoneyFromChoice IdentChoice
                    Person
                    Money
  deriving (Eq)

showMoney :: Money -> String
showMoney (AvailableMoney (IdentCC icc)) =
  "(AvailableMoney (IdentCC " ++ show icc ++ "))"
showMoney (AddMoney m1 m2) =
  "(AddMoney " ++ showMoney m1 ++ " " ++ showMoney m2 ++ ")"
showMoney (ConstMoney cash) = "(ConstMoney " ++ show cash ++ ")"
showMoney (MoneyFromChoice (IdentChoice ic) p m) =
  "(MoneyFromChoice (IdentChoice " ++
  show ic ++ ") " ++ show p ++ " " ++ showMoney m ++ ")"

-- Representation of observations over observables and the state.
-- Rendered into predicates by interpretObs.
data Observation
  = BelowTimeout Timeout -- are we still on time for something that expires on Timeout?
  | AndObs Observation
           Observation
  | OrObs Observation
          Observation
  | NotObs Observation
  | PersonChoseThis IdentChoice
                    Person
                    ConcreteChoice
  | PersonChoseSomething IdentChoice
                         Person
  | ValueGE Money
            Money -- is first ammount is greater or equal than the second?
  | TrueObs
  | FalseObs
  deriving (Eq)

showObservation :: Observation -> String
showObservation (BelowTimeout tim) = "(BelowTimeout " ++ (show tim) ++ ")"
showObservation (AndObs obs1 obs2) =
  "(AndObs " ++ (showObservation obs1) ++ " " ++ (showObservation obs2) ++ ")"
showObservation (OrObs obs1 obs2) =
  "(OrObs " ++ (showObservation obs1) ++ " " ++ (showObservation obs2) ++ ")"
showObservation (NotObs obs) = "(NotObs " ++ (showObservation obs) ++ ")"
showObservation (PersonChoseThis (IdentChoice ic) per cho) =
  "(PersonChoseThis (IdentChoice " ++
  (show ic) ++ ") " ++ (show per) ++ " " ++ (show cho) ++ ")"
showObservation (PersonChoseSomething (IdentChoice ic) per) =
  "(PersonChoseSomething (IdentChoice " ++
  (show ic) ++ ") " ++ (show per) ++ ")"
showObservation (ValueGE m1 m2) =
  "(ValueGE " ++ (showMoney m1) ++ " " ++ (showMoney m2) ++ ")"
showObservation TrueObs = "TrueObs"
showObservation FalseObs = "FalseObs"

-- The type of contracts
data Contract
  = Null
  | CommitCash IdentCC
               Person
               Money
               Timeout
               Timeout
               Contract
               Contract
  | RedeemCC IdentCC
             Contract
  | Pay IdentPay
        Person
        Person
        Money
        Timeout
        Contract
  | Both Contract
         Contract
  | Choice Observation
           Contract
           Contract
  | When Observation
         Timeout
         Contract
         Contract
  deriving (Eq)

showContract Null = "Null"
showContract (CommitCash (IdentCC idc) per mon tim1 tim2 con1 con2) =
  "(CommitCash (IdentCC " ++
  (show idc) ++
  ") " ++
  (show per) ++
  " " ++
  (showMoney mon) ++
  " " ++
  (show tim1) ++
  " " ++
  (show tim2) ++
  " " ++ (showContract con1) ++ " " ++ (showContract con2) ++ ")"
showContract (RedeemCC (IdentCC idc) con) =
  "(RedeemCC (IdentCC " ++ (show idc) ++ ") " ++ (showContract con) ++ ")"
showContract (Pay (IdentPay idp) per1 per2 mon tim con) =
  "(Pay (IdentPay " ++
  (show idp) ++
  ") " ++
  (show per1) ++
  " " ++
  (show per2) ++
  " " ++
  (showMoney mon) ++ " " ++ (show tim) ++ " " ++ (showContract con) ++ ")"
showContract (Both con1 con2) =
  "(Both " ++ (showContract con1) ++ " " ++ (showContract con2) ++ ")"
showContract (Choice obs con1 con2) =
  "(Choice " ++
  (showObservation obs) ++
  " " ++ (showContract con1) ++ " " ++ (showContract con2) ++ ")"
showContract (When obs tim con1 con2) =
  "(When " ++
  (showObservation obs) ++
  " " ++
  (show tim) ++
  " " ++ (showContract con1) ++ " " ++ (showContract con2) ++ ")"

------------------------
-- AST dependent code --
------------------------
data ASTNode
  = ASTNodeC Contract
  | ASTNodeO Observation
  | ASTNodeM Money
  | ASTNodeCC IdentCC
  | ASTNodeIC IdentChoice
  | ASTNodeIP IdentPay
  | ASTNodeI Int

listCurryType :: ASTNode -> (String, [ASTNode])
listCurryType (ASTNodeM (AvailableMoney identCC)) =
  ("AvailableMoney", [ASTNodeCC identCC])
listCurryType (ASTNodeM (AddMoney money1 money2)) =
  ("AddMoney", [ASTNodeM money1, ASTNodeM money2])
listCurryType (ASTNodeM (ConstMoney cash)) = ("ConstMoney", [ASTNodeI cash])
listCurryType (ASTNodeM (MoneyFromChoice identChoice person def)) =
  ("MoneyFromChoice", [ASTNodeIC identChoice, ASTNodeI person, ASTNodeM def])
listCurryType (ASTNodeO (BelowTimeout timeout)) =
  ("BelowTimeout", [ASTNodeI timeout])
listCurryType (ASTNodeO (AndObs observation1 observation2)) =
  ("AndObs", [ASTNodeO observation1, ASTNodeO observation2])
listCurryType (ASTNodeO (OrObs observation1 observation2)) =
  ("OrObs", [ASTNodeO observation1, ASTNodeO observation2])
listCurryType (ASTNodeO (NotObs observation)) =
  ("NotObs", [ASTNodeO observation])
listCurryType (ASTNodeO (PersonChoseThis identChoice person concreteChoice)) =
  ( "PersonChoseThis"
  , [ASTNodeIC identChoice, ASTNodeI person, ASTNodeI concreteChoice])
listCurryType (ASTNodeO (PersonChoseSomething identChoice person)) =
  ("PersonChoseSomething", [ASTNodeIC identChoice, ASTNodeI person])
listCurryType (ASTNodeO (ValueGE money1 money2)) =
  ("ValueGE", [ASTNodeM money1, ASTNodeM money2])
listCurryType (ASTNodeO TrueObs) = ("TrueObs", [])
listCurryType (ASTNodeO FalseObs) = ("FalseObs", [])
listCurryType (ASTNodeC Null) = ("Null", [])
listCurryType (ASTNodeC (CommitCash identCC person cash timeout1 timeout2 contract1 contract2)) =
  ( "CommitCash"
  , [ ASTNodeCC identCC
    , ASTNodeI person
    , ASTNodeM cash
    , ASTNodeI timeout1
    , ASTNodeI timeout2
    , ASTNodeC contract1
    , ASTNodeC contract2
    ])
listCurryType (ASTNodeC (RedeemCC identCC contract)) =
  ("RedeemCC", [ASTNodeCC identCC, ASTNodeC contract])
listCurryType (ASTNodeC (Pay identPay person1 person2 cash timeout contract)) =
  ( "Pay"
  , [ ASTNodeIP identPay
    , ASTNodeI person1
    , ASTNodeI person2
    , ASTNodeM cash
    , ASTNodeI timeout
    , ASTNodeC contract
    ])
listCurryType (ASTNodeC (Both contract1 contract2)) =
  ("Both", [ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeC (Choice observation contract1 contract2)) =
  ("Choice", [ASTNodeO observation, ASTNodeC contract1, ASTNodeC contract2])
listCurryType (ASTNodeC (When observation timeout contract1 contract2)) =
  ( "When"
  , [ ASTNodeO observation
    , ASTNodeI timeout
    , ASTNodeC contract1
    , ASTNodeC contract2
    ])
listCurryType (ASTNodeCC (IdentCC int)) = ("IdentCC", [ASTNodeI int])
listCurryType (ASTNodeIC (IdentChoice int)) = ("IdentChoice", [ASTNodeI int])
listCurryType (ASTNodeIP (IdentPay int)) = ("IdentPay", [ASTNodeI int])
listCurryType (ASTNodeI int) = (show int, [])

isComplex :: ASTNode -> Bool
isComplex (ASTNodeO _) = True
isComplex (ASTNodeC _) = True
isComplex (ASTNodeM _) = True
isComplex _            = False

--------------------------
-- AST independent code --
--------------------------
data NodeType
  = Trivial (String, [ASTNode])
  | Simple (String, [ASTNode])
  | Complex (String, [ASTNode])

tabulateLine :: Int -> String
tabulateLine n = replicate n ' '

classify :: ASTNode -> NodeType
classify x
  | null $ snd r = Trivial r
  | isComplex x = Complex r
  | otherwise = Simple r
    where
        r = listCurryType x

isTrivial :: NodeType -> Bool
isTrivial (Trivial _) = True
isTrivial _           = False

noneComplex :: NodeType -> NodeType -> Bool
noneComplex (Complex _) _ = False
noneComplex _ (Complex _) = False
noneComplex _ _           = True

-- We assume that Simple nodes have Simple or Trivial children
smartPrettyPrint :: Int -> NodeType -> String
smartPrettyPrint _ (Trivial a)      = prettyPrint 0 a
smartPrettyPrint _ (Simple a)       = "(" ++ prettyPrint 0 a ++ ")"
smartPrettyPrint spaces (Complex a) = "(" ++ prettyPrint (spaces + 1) a ++ ")"

prettyPrint :: Int -> (String, [ASTNode]) -> String
prettyPrint _ (name, []) = name
prettyPrint spaces (name, args) =
    intercalate "\n" (trivialNames : map (tabulateLine newSpaces ++) others)
    where
      classified = map classify args
      newSpaces = spaces + length name + 1
      groupedClassified = groupBy noneComplex classified
      trivialNames =
          unwords
              (name : map (smartPrettyPrint newSpaces) (head groupedClassified))
      others =
          map
              (unwords . map (smartPrettyPrint newSpaces))
              (tail groupedClassified)

-------------
-- Wrapper --
-------------
prettyPrintContract :: Contract -> String
prettyPrintContract = prettyPrint 0 . listCurryType . ASTNodeC

