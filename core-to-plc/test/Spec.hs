{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

module Main (main) where

import           Language.Plutus.CoreToPLC.Plugin
import           Language.Plutus.CoreToPLC.Primitives as Prims

import           Language.PlutusCore

import           Test.Tasty
import           Test.Tasty.Golden

import qualified Data.ByteString                      as BS
import qualified Data.ByteString.Lazy                 as BSL
import           Data.Text.Encoding                   (encodeUtf8)

main :: IO ()
main = defaultMain tests

golden :: String -> PlcCode -> TestTree
golden name value = (goldenVsString name ("test/" ++ name ++ ".plc.golden") . pure . BSL.fromStrict . encodeUtf8 . debugText . getAst) value

tests :: TestTree
tests = testGroup "GHC Core to PLC conversion" [
    basic
  , primitives
  , structure
  , datat
  , recursion
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
  , golden "bool" bool
  , golden "tuple" tuple
  , golden "tupleMatch" tupleMatch
  , golden "intCompare" intCompare
  , golden "intEq" intEq
  , golden "intPlus" intPlus
  , golden "error" errorPlc
  , golden "blocknum" blocknumPlc
  , golden "bytestring" bytestring
  , golden "verify" verify
  ]

string :: PlcCode
string = plc "test"

int :: PlcCode
int = plc (1::Int)

bool :: PlcCode
bool = plc True

tuple :: PlcCode
tuple = plc ((1::Int), (2::Int))

tupleMatch :: PlcCode
tupleMatch = plc (\(x:: (Int, Int)) -> let (a, b) = x in a)

intCompare :: PlcCode
intCompare = plc (\(x::Int) (y::Int) -> x < y)

intEq :: PlcCode
intEq = plc (\(x::Int) (y::Int) -> x == y)

intPlus :: PlcCode
intPlus = plc (\(x::Int) (y::Int) -> x + y)

errorPlc :: PlcCode
errorPlc = plc (Prims.error @Int)

blocknumPlc :: PlcCode
blocknumPlc = plc Prims.blocknum

bytestring :: PlcCode
bytestring = plc (\(x::Prims.ByteString) -> x)

verify :: PlcCode
verify = plc (\(x::Prims.ByteString) (y::Prims.ByteString) (z::Prims.ByteString) -> Prims.verifySignature x y z)

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
  ]

monoData :: TestTree
monoData = testGroup "Monomorphic data" [
    golden "enum" basicEnum
  , golden "monoDataType" monoDataType
  , golden "monoConstructor" monoConstructor
  , golden "monoConstructed" monoConstructed
  , golden "monoCase" monoCase
  , golden "defaultCase" defaultCase
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
defaultCase = plc (\(x :: MyMonoData) -> case x of { Mono2 a -> a ; _ -> 1; })

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

recursion :: TestTree
recursion = testGroup "Recursive functions" [
    golden "fib" fib
  ]

fib :: PlcCode
-- not using case to avoid literal cases
fib = plc (let fib :: Int -> Int
               fib n = if n == 0 then 0 else if n == 1 then 1 else fib(n-1) + fib(n-2)
           in fib 4)
