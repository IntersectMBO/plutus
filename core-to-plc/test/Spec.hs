{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:defer-errors #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

module Main (main) where

import           IllTyped

import           Language.Plutus.CoreToPLC.Plugin
import qualified Language.Plutus.CoreToPLC.Primitives     as Prims

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine
import qualified Language.PlutusCore.Pretty               as PLC

import           Test.Tasty
import           Test.Tasty.Golden

import           Control.Exception
import           Control.Monad.Except                     hiding (void)

import qualified Data.ByteString.Lazy                     as BSL
import qualified Data.Text                                as T
import           Data.Text.Encoding                       (encodeUtf8)

-- this module does lots of weird stuff deliberately
{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = defaultMain tests

getPlc :: PlcCode -> ExceptT BSL.ByteString IO (Program TyName Name ())
getPlc value = withExceptT (strToBs . show) $ getAst <$> (ExceptT $ try @SomeException (evaluate value))

goldenVsPretty :: PLC.PrettyPlc a => String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty name value = goldenVsString name ("test/" ++ name ++ ".plc.golden") $ either id (txtToBs . PLC.docText . PLC.prettyPlcClassicDebug) <$> runExceptT value

golden :: String -> PlcCode -> TestTree
golden name value = goldenVsPretty name (getPlc value)

goldenEvalApp :: String -> [PlcCode] -> TestTree
goldenEvalApp name values = goldenVsPretty name $ runCk <$> do
    ps <- mapM getPlc values
    pure $ foldl1 (\acc p -> applyProgram acc p) ps

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . encodeUtf8 . T.pack

txtToBs :: T.Text -> BSL.ByteString
txtToBs = BSL.fromStrict . encodeUtf8

tests :: TestTree
tests = testGroup "GHC Core to PLC conversion" [
    basic
  , primitives
  , structure
  , datat
  , recursiveTypes
  , recursion
  , errors
  ]

basic :: TestTree
basic = testGroup "Basic functions" [
    golden "monoId" monoId
  , golden "monoK" monoK
  ]

monoId :: PlcCode
monoId = plc (\(x :: Int) -> x)

monoK :: PlcCode
monoK = plc (\(i :: Int) -> \(j :: Int) -> i)

primitives :: TestTree
primitives = testGroup "Primitive types and operations" [
    golden "string" string
  , golden "int" int
  , golden "int2" int
  , golden "bool" bool
  , golden "and" andPlc
  , goldenEvalApp "andApply" [ andPlc, plc True, plc False ]
  , golden "tuple" tuple
  , golden "tupleMatch" tupleMatch
  , goldenEvalApp "tupleConstDest" [ tupleMatch, tuple ]
  , golden "intCompare" intCompare
  , golden "intEq" intEq
  , goldenEvalApp "intEqApply" [ intEq, int, int ]
  , golden "void" void
  , golden "intPlus" intPlus
  , goldenEvalApp "intPlusApply" [ intPlus, int, int2 ]
  , golden "error" errorPlc
  , golden "ifThenElse" ifThenElse
  , goldenEvalApp "ifThenElseApply" [ ifThenElse, int, int2 ]
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

structure :: TestTree
structure = testGroup "Structures" [
    golden "letFun" letFun
  ]

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: PlcCode
letFun = plc (\(x::Int) (y::Int) -> let f z = x == z in f y)

datat :: TestTree
datat = testGroup "Data" [
    monoData
  , polyData
  , newtypes
  ]

monoData :: TestTree
monoData = testGroup "Monomorphic data" [
    golden "enum" basicEnum
  , golden "monoDataType" monoDataType
  , golden "monoConstructor" monoConstructor
  , golden "monoConstructed" monoConstructed
  , golden "monoCase" monoCase
  , goldenEvalApp "monoConstDest" [ monoCase, monoConstructed ]
  , golden "defaultCase" defaultCase
  , goldenEvalApp "monoConstDestDefault" [ monoCase, monoConstructed ]
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

polyData :: TestTree
polyData = testGroup "Polymorphic data" [
    golden "polyDataType" polyDataType
  , golden "polyConstructed" polyConstructed
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: PlcCode
polyDataType = plc (\(x:: MyPolyData Int Int) -> x)

polyConstructed :: PlcCode
polyConstructed = plc (Poly1 (1::Int) (2::Int))

newtypes :: TestTree
newtypes = testGroup "Newtypes" [
    golden "basicNewtype" basicNewtype
   , golden "newtypeMatch" newtypeMatch
   , golden "newtypeCreate" newtypeCreate
   , golden "newtypeCreate2" newtypeCreate2
   , golden "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenEvalApp "newtypeCreatDest" [ newtypeMatch, newtypeCreate2 ]
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

recursiveTypes :: TestTree
recursiveTypes = testGroup "Recursive types" [
    golden "listConstruct" listConstruct
    , golden "listConstruct2" listConstruct2
    , golden "listMatch" listMatch
    , goldenEvalApp "listConstDest" [ listMatch, listConstruct ]
    , goldenEvalApp "listConstDest2" [ listMatch, listConstruct2 ]
    , golden "ptreeConstruct" ptreeConstruct
    , golden "ptreeMatch" ptreeMatch
    , goldenEvalApp "ptreeConstDest" [ ptreeMatch, ptreeConstruct ]
  ]

recursion :: TestTree
recursion = testGroup "Recursive functions" [
    -- currently broken, will come back to this later
    --golden "fib" fib
  ]

fib :: PlcCode
-- not using case to avoid literal cases
fib = plc (let fib :: Int -> Int
               fib n = if n == 0 then 0 else if n == 1 then 1 else fib(n-1) + fib(n-2)
           in fib 4)

errors :: TestTree
errors = testGroup "Errors" [
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
