{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:strip-context #-}
-- the simplifier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
-- this adds source notes which helps the plugin give better errors
{-# OPTIONS_GHC   -g #-}

module Plugin.Spec where

import           Common
import           PlcTestUtils

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift
import           Language.PlutusTx.Plugin

import           Data.ByteString.Lazy
import           Data.Text.Prettyprint.Doc
import           GHC.Generics

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

instance GetProgram (CompiledCode a) where
    getProgram = catchAll . getPlc

goldenPir :: String -> CompiledCode a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty $ getPir value

tests :: TestNested
tests = testNested "Plugin" [
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
    goldenPlc "monoId" monoId
  , goldenPlc "monoK" monoK
  ]

monoId :: CompiledCode (Int -> Int)
monoId = plc @"monoId" (\(x :: Int) -> x)

monoK :: CompiledCode (Int -> Int -> Int)
monoK = plc @"monoK" (\(i :: Int) -> \(j :: Int) -> i)

primitives :: TestNested
primitives = testNested "primitives" [
-- ?????
--     goldenPir "string" string
    goldenPir "int" int
  , goldenPir "int2" int
  , goldenPir "bool" bool
  , goldenPir "and" andPlc
  , goldenEval "andApply" [ getProgram $ andPlc, getProgram $ plc @"T" True, getProgram $ plc @"F" False ]
  , goldenPir "tuple" tuple
  , goldenPir "tupleMatch" tupleMatch
  , goldenEval "tupleConstDest" [ getProgram $ tupleMatch, getProgram $ tuple ]
  , goldenPir "intCompare" intCompare
  , goldenPir "intEq" intEq
  , goldenEval "intEqApply" [ getProgram $ intEq, getProgram $ int, getProgram $ int ]
  , goldenPir "void" void
  , goldenPir "intPlus" intPlus
  , goldenPir "intDiv" intDiv
  , goldenEval "intPlusApply" [ getProgram $ intPlus, getProgram $ int, getProgram $ int2 ]
  , goldenPir "error" errorPlc
  , goldenPir "ifThenElse" ifThenElse
  , goldenEval "ifThenElseApply" [ getProgram $ ifThenElse, getProgram $ int, getProgram $ int2 ]
  --, goldenPlc "blocknum" blocknumPlc
  , goldenPir "bytestring" bytestring
  , goldenEval "bytestringApply" [ getPlc bytestring, unsafeLiftProgram ("hello"::ByteString) ]
  , goldenEval "sha2_256" [ getPlc sha2, unsafeLiftProgram ("hello" :: ByteString)]
  , goldenEval "equalsByteString" [ getPlc bsEquals, unsafeLiftProgram ("hello" :: ByteString), unsafeLiftProgram ("hello" :: ByteString)]
  , goldenPir "verify" verify
  ]

int :: CompiledCode Int
int = plc @"int" (1::Int)

int2 :: CompiledCode Int
int2 = plc @"int2" (2::Int)

bool :: CompiledCode Bool
bool = plc @"bool" True

andPlc :: CompiledCode (Bool -> Bool -> Bool)
andPlc = plc @"andPlc" (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode (Int, Int)
tuple = plc @"tuple" ((1::Int), (2::Int))

tupleMatch :: CompiledCode ((Int, Int) -> Int)
tupleMatch = plc @"tupleMatch" (\(x:: (Int, Int)) -> let (a, b) = x in a)

intCompare :: CompiledCode (Int -> Int -> Bool)
intCompare = plc @"intCompare" (\(x::Int) (y::Int) -> x < y)

intEq :: CompiledCode (Int -> Int -> Bool)
intEq = plc @"intEq" (\(x::Int) (y::Int) -> x == y)

-- Has a Void in it
void :: CompiledCode (Int -> Int -> Bool)
void = plc @"void" (\(x::Int) (y::Int) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in (x == y) `a` (y == x))

intPlus :: CompiledCode (Int -> Int -> Int)
intPlus = plc @"intPlus" (\(x::Int) (y::Int) -> x + y)

intDiv :: CompiledCode (Int -> Int -> Int)
intDiv = plc @"intDiv" (\(x::Int) (y::Int) -> x `div` y)

errorPlc :: CompiledCode (() -> Int)
errorPlc = plc @"errorPlc" (Builtins.error @Int)

ifThenElse :: CompiledCode (Int -> Int -> Int)
ifThenElse = plc @"ifThenElse" (\(x::Int) (y::Int) -> if x == y then x else y)

--blocknumPlc :: CompiledCode
--blocknumPlc = plc @"blocknumPlc" Builtins.blocknum

bytestring :: CompiledCode (ByteString -> ByteString)
bytestring = plc @"bytestring" (\(x::ByteString) -> x)

sha2 :: CompiledCode (ByteString -> ByteString)
sha2 = plc @"sha2" (\(x :: ByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode (ByteString -> ByteString -> Bool)
bsEquals = plc @"bsEquals" (\(x :: ByteString) (y :: ByteString) -> Builtins.equalsByteString x y)

verify :: CompiledCode (ByteString -> ByteString -> ByteString -> Bool)
verify = plc @"verify" (\(x::ByteString) (y::ByteString) (z::ByteString) -> Builtins.verifySignature x y z)

structure :: TestNested
structure = testNested "structure" [
    goldenPlc "letFun" letFun
  ]

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Int -> Int -> Bool)
letFun = plc @"lefFun" (\(x::Int) (y::Int) -> let f z = x == z in f y)

datat :: TestNested
datat = testNested "data" [
    monoData
  , polyData
  , newtypes
  ]

monoData :: TestNested
monoData = testNested "monomorphic" [
    goldenPir "enum" basicEnum
  , goldenPir "monoDataType" monoDataType
  , goldenPir "monoConstructor" monoConstructor
  , goldenPir "monoConstructed" monoConstructed
  , goldenPir "monoCase" monoCase
  , goldenEval "monoConstDest" [ getProgram $ monoCase, getProgram $ monoConstructed ]
  , goldenPir "defaultCase" defaultCase
  , goldenPir "irrefutableMatch" irrefutableMatch
  , goldenPir "atPattern" atPattern
  , goldenEval "monoConstDestDefault" [ getProgram $ monoCase, getProgram $ monoConstructed ]
  , goldenPir "monoRecord" monoRecord
  , goldenPir "nonValueCase" nonValueCase
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode MyEnum
basicEnum = plc @"basicEnum" (Enum1)

data MyMonoData = Mono1 Int Int | Mono2 Int | Mono3 Int deriving (Generic)

monoDataType :: CompiledCode (MyMonoData -> MyMonoData)
monoDataType = plc @"monoDataType" (\(x :: MyMonoData) -> x)

monoConstructor :: CompiledCode (Int -> Int -> MyMonoData)
monoConstructor = plc @"monConstructor" (Mono1)

monoConstructed :: CompiledCode MyMonoData
monoConstructed = plc @"monoConstructed" (Mono2 1)

monoCase :: CompiledCode (MyMonoData -> Int)
monoCase = plc @"monoCase" (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: CompiledCode (MyMonoData -> Int)
defaultCase = plc @"defaultCase" (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: CompiledCode (MyMonoData -> Int)
irrefutableMatch = plc @"irrefutableMatch" (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

atPattern :: CompiledCode ((Int, Int) -> Int)
atPattern = plc @"atPattern" (\t@(x::Int, y::Int) -> let fst (a, b) = a in y + fst t)

data MyMonoRecord = MyMonoRecord { mrA :: Int , mrB :: Int} deriving Generic

monoRecord :: CompiledCode (MyMonoRecord -> MyMonoRecord)
monoRecord = plc @"monoRecord" (\(x :: MyMonoRecord) -> x)

-- must be compiled with a lazy case
nonValueCase :: CompiledCode (MyEnum -> Int)
nonValueCase = plc @"nonValueCase" (\(x :: MyEnum) -> case x of { Enum1 -> 1::Int ; Enum2 -> Builtins.error (); })

type Synonym = Int

synonym :: CompiledCode Int
synonym = plc @"synonym" (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPir "polyDataType" polyDataType
  , goldenPir "polyConstructed" polyConstructed
  , goldenPir "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: CompiledCode (MyPolyData Int Int -> MyPolyData Int Int)
polyDataType = plc @"polyDataType" (\(x:: MyPolyData Int Int) -> x)

polyConstructed :: CompiledCode (MyPolyData Int Int)
polyConstructed = plc @"polyConstructed" (Poly1 (1::Int) (2::Int))

defaultCasePoly :: CompiledCode (MyPolyData Int Int -> Int)
defaultCasePoly = plc @"defaultCasePoly" (\(x :: MyPolyData Int Int) -> case x of { Poly1 a _ -> a ; _ -> 2; })

newtypes :: TestNested
newtypes = testNested "newtypes" [
    goldenPir "basicNewtype" basicNewtype
   , goldenPir "newtypeMatch" newtypeMatch
   , goldenPir "newtypeCreate" newtypeCreate
   , goldenPir "newtypeCreate2" newtypeCreate2
   , goldenPir "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenEval "newtypeCreatDest" [ getProgram $ newtypeMatch, getProgram $ newtypeCreate2 ]
   ]

newtype MyNewtype = MyNewtype Int

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: CompiledCode (MyNewtype -> MyNewtype)
basicNewtype = plc @"basicNewtype" (\(x::MyNewtype) -> x)

newtypeMatch :: CompiledCode (MyNewtype -> Int)
newtypeMatch = plc @"newtypeMatch" (\(MyNewtype x) -> x)

newtypeCreate :: CompiledCode (Int -> MyNewtype)
newtypeCreate = plc @"newtypeCreate" (\(x::Int) -> MyNewtype x)

newtypeCreate2 :: CompiledCode MyNewtype
newtypeCreate2 = plc @"newtypeCreate2" (MyNewtype 1)

nestedNewtypeMatch :: CompiledCode (MyNewtype2 -> Int)
nestedNewtypeMatch = plc @"nestedNewtypeMatch" (\(MyNewtype2 (MyNewtype x)) -> x)

recursiveTypes :: TestNested
recursiveTypes = testNested "recursiveTypes" [
    goldenPir "listConstruct" listConstruct
    , goldenPir "listConstruct2" listConstruct2
    , goldenPir "listConstruct3" listConstruct3
    , goldenPir "listMatch" listMatch
    , goldenEval "listConstDest" [ getProgram $ listMatch, getProgram $ listConstruct ]
    , goldenEval "listConstDest2" [ getProgram $ listMatch, getProgram $ listConstruct2 ]
    , goldenPir "ptreeConstruct" ptreeConstruct
    , goldenPir "ptreeMatch" ptreeMatch
    , goldenEval "ptreeConstDest" [ getProgram $ ptreeMatch, getProgram $ ptreeConstruct ]
  ]

listConstruct :: CompiledCode [Int]
listConstruct = plc @"listConstruct" ([]::[Int])

listConstruct2 :: CompiledCode [Int]
listConstruct2 = plc @"listConstruct2" ([1]::[Int])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode [Int]
listConstruct3 = plc @"listConstruct3" ((1::Int):(2::Int):(3::Int):[])

listMatch :: CompiledCode ([Int] -> Int)
listMatch = plc @"listMatch" (\(l::[Int]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode (B Int)
ptreeConstruct = plc @"ptreeConstruct" (Two (Two (One ((1,2),(3,4)))) :: B Int)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode (B Int -> Int)
ptreeMatch = plc @"ptreeMatch" (\(t::B Int) -> case t of { One a -> a; Two _ -> 2; })

recursion :: TestNested
recursion = testNested "recursiveFunctions" [
    -- currently broken, will come back to this later
    goldenPir "fib" fib
    , goldenEval "fib4" [ getProgram $ fib, getProgram $ plc @"4" (4::Int) ]
    , goldenPir "sum" sumDirect
    , goldenEval "sumList" [ getProgram $ sumDirect, getProgram $ listConstruct3 ]
    --, golden "sumFold" sumViaFold
    --, goldenEval "sumFoldList" [ sumViaFold, listConstruct3 ]
    , goldenPir "even" evenMutual
    , goldenEval "even3" [ getProgram $ evenMutual, getProgram $ plc @"3" (3::Int) ]
    , goldenEval "even4" [ getProgram $ evenMutual, getProgram $ plc @"4" (4::Int) ]
  ]

fib :: CompiledCode (Int -> Int)
-- not using case to avoid literal cases
fib = plc @"fib" (
    let fib :: Int -> Int
        fib n = if n == 0 then 0 else if n == 1 then 1 else fib(n-1) + fib(n-2)
    in fib)

sumDirect :: CompiledCode ([Int] -> Int)
sumDirect = plc @"sumDirect" (
    let sum :: [Int] -> Int
        sum []     = 0
        sum (x:xs) = x + sum xs
    in sum)

evenMutual :: CompiledCode (Int -> Bool)
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
    , goldenPlcCatch "recordSelector" recordSelector
  ]

integer :: CompiledCode Integer
integer = plc @"integer" (1::Integer)

free :: CompiledCode Bool
free = plc @"free" (True && False)

-- It's little tricky to get something that GHC actually turns into a polymorphic computation! We use our value twice
-- at different types to prevent the obvious specialization.
valueRestriction :: CompiledCode (Bool, Int)
valueRestriction = plc @"valueRestriction" (let { f :: forall a . a; f = Builtins.error (); } in (f @Bool, f @Int))

recordSelector :: CompiledCode (MyMonoRecord -> Int)
recordSelector = plc @"recordSelector" (\(x :: MyMonoRecord) -> mrA x)
