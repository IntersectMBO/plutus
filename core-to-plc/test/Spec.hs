{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:defer-errors #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

module Main (main) where

import           IllTyped

import           Common
import           PlutusPrelude                            (bsToStr, strToBs)

import           Language.Plutus.CoreToPLC.Plugin
import qualified Language.Plutus.CoreToPLC.Primitives     as Prims

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine
import qualified Language.PlutusCore.Pretty               as PLC

import           Test.Tasty

import           Control.Exception
import           Control.Monad.Except                     hiding (void)

import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text.Prettyprint.Doc                as PP

-- this module does lots of weird stuff deliberately
{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = defaultMain $ runTestNestedIn ["test"] tests

getPlc :: PlcCode -> ExceptT BSL.ByteString IO (Program TyName Name ())
getPlc value = withExceptT (strToBs . show) $ getAst <$> (ExceptT $ try @SomeException (evaluate value))

runPlc :: [PlcCode] -> ExceptT BSL.ByteString IO EvaluationResult
runPlc values = runCk <$> do
    ps <- mapM getPlc values
    pure $ foldl1 (\acc p -> applyProgram acc p) ps

golden :: String -> PlcCode -> TestNested
golden name value = nestedGoldenVsDocM name $ either (PP.pretty . bsToStr) (PLC.prettyPlcClassicDebug) <$> (runExceptT $ getPlc value)

goldenEval :: String -> [PlcCode] -> TestNested
goldenEval name values = nestedGoldenVsDocM name $ either (PP.pretty . bsToStr) (PLC.prettyPlcClassicDebug) <$> (runExceptT $ runPlc values)

tests :: TestNested
tests = testGroup "conversion" <$> sequence [
    basic
  , primitives
  , structure
  , datat
  , recursiveTypes
  , recursion
  , errors
  ]

basic :: TestNested
basic = testNested "basic" [
    golden "monoId" monoId
  , golden "monoK" monoK
  ]

monoId :: PlcCode
monoId = plc (\(x :: Int) -> x)

monoK :: PlcCode
monoK = plc (\(i :: Int) -> \(j :: Int) -> i)

primitives :: TestNested
primitives = testNested "primitives" [
    golden "string" string
  , golden "int" int
  , golden "int2" int
  , golden "bool" bool
  , golden "and" andPlc
  , goldenEval "andApply" [ andPlc, plc True, plc False ]
  , golden "tuple" tuple
  , golden "tupleMatch" tupleMatch
  , goldenEval "tupleConstDest" [ tupleMatch, tuple ]
  , golden "intCompare" intCompare
  , golden "intEq" intEq
  , goldenEval "intEqApply" [ intEq, int, int ]
  , golden "void" void
  , golden "intPlus" intPlus
  , goldenEval "intPlusApply" [ intPlus, int, int2 ]
  , golden "error" errorPlc
  , golden "ifThenElse" ifThenElse
  , goldenEval "ifThenElseApply" [ ifThenElse, int, int2 ]
  , golden "blocknum" blocknumPlc
  , golden "bytestring" bytestring
  , golden "verify" verify
  ]

string :: PlcCode
string = plc "test"

int :: PlcCode
int = plc (1::Int)

int2 :: PlcCode
int2 = plc (2::Int)

bool :: PlcCode
bool = plc True

andPlc :: PlcCode
andPlc = plc (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: PlcCode
tuple = plc ((1::Int), (2::Int))

tupleMatch :: PlcCode
tupleMatch = plc (\(x:: (Int, Int)) -> let (a, b) = x in a)

intCompare :: PlcCode
intCompare = plc (\(x::Int) (y::Int) -> x < y)

intEq :: PlcCode
intEq = plc (\(x::Int) (y::Int) -> x == y)

-- Has a Void in it
void :: PlcCode
void = plc (\(x::Int) (y::Int) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in (x == y) `a` (y == x))

intPlus :: PlcCode
intPlus = plc (\(x::Int) (y::Int) -> x + y)

errorPlc :: PlcCode
errorPlc = plc (Prims.error @Int)

ifThenElse :: PlcCode
ifThenElse = plc (\(x::Int) (y::Int) -> if x == y then x else y)

blocknumPlc :: PlcCode
blocknumPlc = plc Prims.blocknum

bytestring :: PlcCode
bytestring = plc (\(x::Prims.ByteString) -> x)

verify :: PlcCode
verify = plc (\(x::Prims.ByteString) (y::Prims.ByteString) (z::Prims.ByteString) -> Prims.verifySignature x y z)

structure :: TestNested
structure = testNested "structure" [
    golden "letFun" letFun
  ]

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: PlcCode
letFun = plc (\(x::Int) (y::Int) -> let f z = x == z in f y)

datat :: TestNested
datat = testNested "data" [
    monoData
  , polyData
  , newtypes
  ]

monoData :: TestNested
monoData = testNested "monomorphic" [
    golden "enum" basicEnum
  , golden "monoDataType" monoDataType
  , golden "monoConstructor" monoConstructor
  , golden "monoConstructed" monoConstructed
  , golden "monoCase" monoCase
  , goldenEval "monoConstDest" [ monoCase, monoConstructed ]
  , golden "defaultCase" defaultCase
  , goldenEval "monoConstDestDefault" [ monoCase, monoConstructed ]
  , golden "nonValueCase" nonValueCase
  , golden "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: PlcCode
basicEnum = plc (Enum1)

data MyMonoData = Mono1 Int Int | Mono2 Int | Mono3 Int

monoDataType :: PlcCode
monoDataType = plc (\(x:: MyMonoData) -> x)

monoConstructor :: PlcCode
monoConstructor = plc (Mono1)

monoConstructed :: PlcCode
monoConstructed = plc (Mono2 1)

monoCase :: PlcCode
monoCase = plc (\(x :: MyMonoData) -> case x of { Mono1 a b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: PlcCode
defaultCase = plc (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

-- must be compiled with a lazy case
nonValueCase :: PlcCode
nonValueCase = plc (\(x :: MyEnum) -> case x of { Enum1 -> 1::Int ; Enum2 -> Prims.error (); })

type Synonym = Int

synonym :: PlcCode
synonym = plc (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    golden "polyDataType" polyDataType
  , golden "polyConstructed" polyConstructed
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: PlcCode
polyDataType = plc (\(x:: MyPolyData Int Int) -> x)

polyConstructed :: PlcCode
polyConstructed = plc (Poly1 (1::Int) (2::Int))

newtypes :: TestNested
newtypes = testNested "newtypes" [
    golden "basicNewtype" basicNewtype
   , golden "newtypeMatch" newtypeMatch
   , golden "newtypeCreate" newtypeCreate
   , golden "newtypeCreate2" newtypeCreate2
   , golden "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenEval "newtypeCreatDest" [ newtypeMatch, newtypeCreate2 ]
   ]

newtype MyNewtype = MyNewtype Int

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: PlcCode
basicNewtype = plc (\(x::MyNewtype) -> x)

newtypeMatch :: PlcCode
newtypeMatch = plc (\(MyNewtype x) -> x)

newtypeCreate :: PlcCode
newtypeCreate = plc (\(x::Int) -> MyNewtype x)

newtypeCreate2 :: PlcCode
newtypeCreate2 = plc (MyNewtype 1)

nestedNewtypeMatch :: PlcCode
nestedNewtypeMatch = plc (\(MyNewtype2 (MyNewtype x)) -> x)

recursiveTypes :: TestNested
recursiveTypes = testNested "recursiveTypes" [
    golden "listConstruct" listConstruct
    , golden "listConstruct2" listConstruct2
    , golden "listConstruct3" listConstruct3
    , golden "listMatch" listMatch
    , goldenEval "listConstDest" [ listMatch, listConstruct ]
    , goldenEval "listConstDest2" [ listMatch, listConstruct2 ]
    , golden "ptreeConstruct" ptreeConstruct
    , golden "ptreeMatch" ptreeMatch
    , goldenEval "ptreeConstDest" [ ptreeMatch, ptreeConstruct ]
  ]

recursion :: TestNested
recursion = testNested "recursiveFunctions" [
    -- currently broken, will come back to this later
    golden "fib" fib
    , goldenEval "fib4" [ fib, plc (4::Int) ]
    , golden "sum" sumDirect
    , goldenEval "sumList" [ sumDirect, listConstruct3 ]
    --, golden "sumFold" sumViaFold
    --, goldenEval "sumFoldList" [ sumViaFold, listConstruct3 ]
    , golden "even" evenMutual
    , goldenEval "even3" [ evenMutual, plc (3::Int) ]
    , goldenEval "even4" [ evenMutual, plc (4::Int) ]
  ]

fib :: PlcCode
-- not using case to avoid literal cases
fib = plc (
    let fib :: Int -> Int
        fib n = if n == 0 then 0 else if n == 1 then 1 else fib(n-1) + fib(n-2)
    in fib)

errors :: TestNested
errors = testNested "errors" [
    golden "integer" integer
    , golden "free" free
    , golden "valueRestriction" valueRestriction
  ]

integer :: PlcCode
integer = plc (1::Integer)

free :: PlcCode
free = plc (True && False)

-- It's little tricky to get something that GHC actually turns into a polymorphic computation! We use our value twice
-- at different types to prevent the obvious specialization.
valueRestriction :: PlcCode
valueRestriction = plc (let { f :: forall a . a; f = Prims.error (); } in (f @Bool, f @Int))
