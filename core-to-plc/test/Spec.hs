{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:defer-errors #-}
-- the simplifier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Main (main) where

import           IllTyped

import           Common
import           PlcTestUtils

import qualified Language.Plutus.CoreToPLC.Builtins as Builtins
import           Language.Plutus.CoreToPLC.Plugin
import           Language.Plutus.Lift

import           Language.PlutusCore

import           Test.Tasty

import           Data.ByteString.Lazy
import           GHC.Generics

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

instance GetProgram PlcCode where
    getProgram = catchAll . getAst

tests :: TestNested
tests = testGroup "conversion" <$> sequence [
    basic
  , primitives
  , structure
  , datat
  , recursiveTypes
  , recursion
  , errors
  , generics
  ]

basic :: TestNested
basic = testNested "basic" [
    goldenPlc "monoId" monoId
  , goldenPlc "monoK" monoK
  ]

monoId :: PlcCode
monoId = plc @"monoId" (\(x :: Int) -> x)

monoK :: PlcCode
monoK = plc @"monoK" (\(i :: Int) -> \(j :: Int) -> i)

primitives :: TestNested
primitives = testNested "primitives" [
    goldenPlc "string" string
  , goldenPlc "int" int
  , goldenPlc "int2" int
  , goldenPlc "bool" bool
  , goldenPlc "and" andPlc
  , goldenEval "andApply" [ andPlc, plc @"T" True, plc @"F" False ]
  , goldenPlc "tuple" tuple
  , goldenPlc "tupleMatch" tupleMatch
  , goldenEval "tupleConstDest" [ tupleMatch, tuple ]
  , goldenPlc "intCompare" intCompare
  , goldenPlc "intEq" intEq
  , goldenEval "intEqApply" [ intEq, int, int ]
  , goldenPlc "void" void
  , goldenPlc "intPlus" intPlus
  , goldenEval "intPlusApply" [ intPlus, int, int2 ]
  , goldenPlc "error" errorPlc
  , goldenPlc "ifThenElse" ifThenElse
  , goldenEval "ifThenElseApply" [ ifThenElse, int, int2 ]
  --, goldenPlc "blocknum" blocknumPlc
  , goldenPlc "bytestring" bytestring
  , goldenEval "bytestringApply" [ getAst bytestring, trivialProgram $ runQuote $ lift ("hello"::ByteString) ]
  , goldenPlc "verify" verify
  ]

string :: PlcCode
string = plc @"string" "test"

int :: PlcCode
int = plc @"int" (1::Int)

int2 :: PlcCode
int2 = plc @"int2" (2::Int)

bool :: PlcCode
bool = plc @"bool" True

andPlc :: PlcCode
andPlc = plc @"andPlc" (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: PlcCode
tuple = plc @"tuple" ((1::Int), (2::Int))

tupleMatch :: PlcCode
tupleMatch = plc @"tupleMatch" (\(x:: (Int, Int)) -> let (a, b) = x in a)

intCompare :: PlcCode
intCompare = plc @"intCompare" (\(x::Int) (y::Int) -> x < y)

intEq :: PlcCode
intEq = plc @"intEq" (\(x::Int) (y::Int) -> x == y)

-- Has a Void in it
void :: PlcCode
void = plc @"void" (\(x::Int) (y::Int) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in (x == y) `a` (y == x))

intPlus :: PlcCode
intPlus = plc @"intPlus" (\(x::Int) (y::Int) -> x + y)

errorPlc :: PlcCode
errorPlc = plc @"errorPlc" (Builtins.error @Int)

ifThenElse :: PlcCode
ifThenElse = plc @"ifThenElse" (\(x::Int) (y::Int) -> if x == y then x else y)

--blocknumPlc :: PlcCode
--blocknumPlc = plc @"blocknumPlc" Builtins.blocknum

bytestring :: PlcCode
bytestring = plc @"bytestring" (\(x::ByteString) -> x)

verify :: PlcCode
verify = plc @"verify" (\(x::ByteString) (y::ByteString) (z::ByteString) -> Builtins.verifySignature x y z)

structure :: TestNested
structure = testNested "structure" [
    goldenPlc "letFun" letFun
  ]

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: PlcCode
letFun = plc @"lefFun" (\(x::Int) (y::Int) -> let f z = x == z in f y)

datat :: TestNested
datat = testNested "data" [
    monoData
  , polyData
  , newtypes
  ]

monoData :: TestNested
monoData = testNested "monomorphic" [
    goldenPlc "enum" basicEnum
  , goldenPlc "monoDataType" monoDataType
  , goldenPlc "monoConstructor" monoConstructor
  , goldenPlc "monoConstructed" monoConstructed
  , goldenPlc "monoCase" monoCase
  , goldenEval "monoConstDest" [ monoCase, monoConstructed ]
  , goldenPlc "defaultCase" defaultCase
  , goldenPlc "irrefutableMatch" irrefutableMatch
  , goldenEval "monoConstDestDefault" [ monoCase, monoConstructed ]
  , goldenPlc "monoRecord" monoRecord
  , goldenPlc "nonValueCase" nonValueCase
  , goldenPlc "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: PlcCode
basicEnum = plc @"basicEnum" (Enum1)

data MyMonoData = Mono1 Int Int | Mono2 Int | Mono3 Int deriving (Generic)

monoDataType :: PlcCode
monoDataType = plc @"monoDataType" (\(x :: MyMonoData) -> x)

monoConstructor :: PlcCode
monoConstructor = plc @"monConstructor" (Mono1)

monoConstructed :: PlcCode
monoConstructed = plc @"monoConstructed" (Mono2 1)

monoCase :: PlcCode
monoCase = plc @"monoCase" (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: PlcCode
defaultCase = plc @"defaultCase" (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: PlcCode
irrefutableMatch = plc @"irrefutableMatch" (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

data MyMonoRecord = MyMonoRecord { a :: Int , b :: Int} deriving Generic

monoRecord :: PlcCode
monoRecord = plc @"monoRecord" (\(x :: MyMonoRecord) -> x)

-- must be compiled with a lazy case
nonValueCase :: PlcCode
nonValueCase = plc @"nonValueCase" (\(x :: MyEnum) -> case x of { Enum1 -> 1::Int ; Enum2 -> Builtins.error (); })

type Synonym = Int

synonym :: PlcCode
synonym = plc @"synonym" (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPlc "polyDataType" polyDataType
  , goldenPlc "polyConstructed" polyConstructed
  , goldenPlc "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: PlcCode
polyDataType = plc @"polyDataType" (\(x:: MyPolyData Int Int) -> x)

polyConstructed :: PlcCode
polyConstructed = plc @"polyConstructed" (Poly1 (1::Int) (2::Int))

defaultCasePoly :: PlcCode
defaultCasePoly = plc @"defaultCasePoly" (\(x :: MyPolyData Int Int) -> case x of { Poly1 a _ -> a ; _ -> 2; })

newtypes :: TestNested
newtypes = testNested "newtypes" [
    goldenPlc "basicNewtype" basicNewtype
   , goldenPlc "newtypeMatch" newtypeMatch
   , goldenPlc "newtypeCreate" newtypeCreate
   , goldenPlc "newtypeCreate2" newtypeCreate2
   , goldenPlc "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenEval "newtypeCreatDest" [ newtypeMatch, newtypeCreate2 ]
   ]

newtype MyNewtype = MyNewtype Int

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: PlcCode
basicNewtype = plc @"basicNewtype" (\(x::MyNewtype) -> x)

newtypeMatch :: PlcCode
newtypeMatch = plc @"newtypeMatch" (\(MyNewtype x) -> x)

newtypeCreate :: PlcCode
newtypeCreate = plc @"newtypeCreate" (\(x::Int) -> MyNewtype x)

newtypeCreate2 :: PlcCode
newtypeCreate2 = plc @"newtypeCreate2" (MyNewtype 1)

nestedNewtypeMatch :: PlcCode
nestedNewtypeMatch = plc @"nestedNewtypeMatch" (\(MyNewtype2 (MyNewtype x)) -> x)

recursiveTypes :: TestNested
recursiveTypes = testNested "recursiveTypes" [
    goldenPlc "listConstruct" listConstruct
    , goldenPlc "listConstruct2" listConstruct2
    , goldenPlc "listConstruct3" listConstruct3
    , goldenPlc "listMatch" listMatch
    , goldenEval "listConstDest" [ listMatch, listConstruct ]
    , goldenEval "listConstDest2" [ listMatch, listConstruct2 ]
    , goldenPlc "ptreeConstruct" ptreeConstruct
    , goldenPlc "ptreeMatch" ptreeMatch
    , goldenEval "ptreeConstDest" [ ptreeMatch, ptreeConstruct ]
  ]

recursion :: TestNested
recursion = testNested "recursiveFunctions" [
    -- currently broken, will come back to this later
    goldenPlc "fib" fib
    , goldenEval "fib4" [ fib, plc @"4" (4::Int) ]
    , goldenPlc "sum" sumDirect
    , goldenEval "sumList" [ sumDirect, listConstruct3 ]
    --, golden "sumFold" sumViaFold
    --, goldenEval "sumFoldList" [ sumViaFold, listConstruct3 ]
    , goldenPlc "even" evenMutual
    , goldenEval "even3" [ evenMutual, plc @"3" (3::Int) ]
    , goldenEval "even4" [ evenMutual, plc @"4" (4::Int) ]
  ]

fib :: PlcCode
-- not using case to avoid literal cases
fib = plc @"fib" (
    let fib :: Int -> Int
        fib n = if n == 0 then 0 else if n == 1 then 1 else fib(n-1) + fib(n-2)
    in fib)

evenMutual :: PlcCode
evenMutual = plc @"evenMutual" (
    let even :: Int -> Bool
        even n = if n == 0 then True else odd (n-1)
        odd :: Int -> Bool
        odd n = if n == 0 then False else even (n-1)
    in even)

errors :: TestNested
errors = testNested "errors" [
    goldenPlcCatch "integer" integer
    , goldenPlcCatch "free" free
    , goldenPlcCatch "valueRestriction" valueRestriction
  ]

integer :: PlcCode
integer = plc @"integer" (1::Integer)

free :: PlcCode
free = plc @"free" (True && False)

-- It's little tricky to get something that GHC actually turns into a polymorphic computation! We use our value twice
-- at different types to prevent the obvious specialization.
valueRestriction :: PlcCode
valueRestriction = plc @"valueRestriction" (let { f :: forall a . a; f = Builtins.error (); } in (f @Bool, f @Int))

instance LiftPlc (MyMonoData)
instance LiftPlc (MyMonoRecord)

generics :: TestNested
generics = testNested "generics" [
    goldenPlc "int" (trivialProgram $ runQuote $ lift (1::Int))
    , goldenPlc "mono" (trivialProgram $ runQuote $ lift (Mono2 2))
    , goldenEval "monoInterop" [ getAst monoCase, (trivialProgram $ runQuote $ lift (Mono1 1 2)) ]
    , goldenPlc "record" (trivialProgram $ runQuote $ lift (MyMonoRecord 1 2))
    , goldenEval "boolInterop" [ getAst andPlc, (trivialProgram $ runQuote $ lift True), (trivialProgram $ runQuote $ lift True) ]
    , goldenPlc "list" (trivialProgram $ runQuote $ lift ([1]::[Int]))
    , goldenEval "listInterop" [ getAst listMatch, (trivialProgram $ runQuote $ lift ([1]::[Int])) ]
    , goldenPlc "liftPlc" (trivialProgram $ runQuote $ lift int)
  ]
