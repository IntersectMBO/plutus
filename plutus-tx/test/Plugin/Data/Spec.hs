{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Data.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

datat :: TestNested
datat = testNested "Data" [
    monoData
  , polyData
  , newtypes
  , recursiveTypes
  ]

monoData :: TestNested
monoData = testNested "monomorphic" [
    goldenPir "enum" basicEnum
  , goldenPir "monoDataType" monoDataType
  , goldenPir "monoConstructor" monoConstructor
  , goldenPir "monoConstructed" monoConstructed
  , goldenPir "monoCase" monoCase
  , goldenEval "monoConstDest" [ getProgram monoCase, getProgram monoConstructed ]
  , goldenPir "defaultCase" defaultCase
  , goldenPir "irrefutableMatch" irrefutableMatch
  , goldenPir "atPattern" atPattern
  , goldenEval "monoConstDestDefault" [ getProgram monoCase, getProgram monoConstructed ]
  , goldenPir "monoRecord" monoRecord
  , goldenPir "recordNewtype" recordNewtype
  , goldenPir "nonValueCase" nonValueCase
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode MyEnum
basicEnum = plc @"basicEnum" Enum1

data MyMonoData = Mono1 Integer Integer | Mono2 Integer | Mono3 Integer
    deriving (Show, Eq)

monoDataType :: CompiledCode (MyMonoData -> MyMonoData)
monoDataType = plc @"monoDataType" (\(x :: MyMonoData) -> x)

monoConstructor :: CompiledCode (Integer -> Integer -> MyMonoData)
monoConstructor = plc @"monConstructor" Mono1

monoConstructed :: CompiledCode MyMonoData
monoConstructed = plc @"monoConstructed" (Mono2 1)

monoCase :: CompiledCode (MyMonoData -> Integer)
monoCase = plc @"monoCase" (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: CompiledCode (MyMonoData -> Integer)
defaultCase = plc @"defaultCase" (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: CompiledCode (MyMonoData -> Integer)
irrefutableMatch = plc @"irrefutableMatch" (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

atPattern :: CompiledCode ((Integer, Integer) -> Integer)
atPattern = plc @"atPattern" (\t@(x::Integer, y::Integer) -> let fst (a, b) = a in Builtins.addInteger y (fst t))

data MyMonoRecord = MyMonoRecord { mrA :: Integer , mrB :: Integer}
    deriving (Show, Eq)

monoRecord :: CompiledCode (MyMonoRecord -> MyMonoRecord)
monoRecord = plc @"monoRecord" (\(x :: MyMonoRecord) -> x)

data RecordNewtype = RecordNewtype { newtypeField :: MyNewtype }

recordNewtype :: CompiledCode (RecordNewtype -> RecordNewtype)
recordNewtype = plc @"recordNewtype" (\(x :: RecordNewtype) -> x)

-- must be compiled with a lazy case
nonValueCase :: CompiledCode (MyEnum -> Integer)
nonValueCase = plc @"nonValueCase" (\(x :: MyEnum) -> case x of { Enum1 -> 1::Integer ; Enum2 -> Builtins.error (); })

type Synonym = Integer

synonym :: CompiledCode Integer
synonym = plc @"synonym" (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPir "polyDataType" polyDataType
  , goldenPir "polyConstructed" polyConstructed
  , goldenPir "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: CompiledCode (MyPolyData Integer Integer -> MyPolyData Integer Integer)
polyDataType = plc @"polyDataType" (\(x:: MyPolyData Integer Integer) -> x)

polyConstructed :: CompiledCode (MyPolyData Integer Integer)
polyConstructed = plc @"polyConstructed" (Poly1 (1::Integer) (2::Integer))

defaultCasePoly :: CompiledCode (MyPolyData Integer Integer -> Integer)
defaultCasePoly = plc @"defaultCasePoly" (\(x :: MyPolyData Integer Integer) -> case x of { Poly1 a _ -> a ; _ -> 2; })

newtypes :: TestNested
newtypes = testNested "newtypes" [
    goldenPir "basicNewtype" basicNewtype
   , goldenPir "newtypeMatch" newtypeMatch
   , goldenPir "newtypeCreate" newtypeCreate
   , goldenPir "newtypeId" newtypeId
   , goldenPir "newtypeCreate2" newtypeCreate2
   , goldenPir "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenEval "newtypeCreatDest" [ getProgram $ newtypeMatch, getProgram $ newtypeCreate2 ]
   , goldenPir "paramNewtype" paramNewtype
   ]

newtype MyNewtype = MyNewtype Integer
    deriving (Show, Eq)

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: CompiledCode (MyNewtype -> MyNewtype)
basicNewtype = plc @"basicNewtype" (\(x::MyNewtype) -> x)

newtypeMatch :: CompiledCode (MyNewtype -> Integer)
newtypeMatch = plc @"newtypeMatch" (\(MyNewtype x) -> x)

newtypeCreate :: CompiledCode (Integer -> MyNewtype)
newtypeCreate = plc @"newtypeCreate" (\(x::Integer) -> MyNewtype x)

newtypeId :: CompiledCode (MyNewtype -> MyNewtype)
newtypeId = plc @"newtypeId" (\(MyNewtype x) -> MyNewtype x)

newtypeCreate2 :: CompiledCode MyNewtype
newtypeCreate2 = plc @"newtypeCreate2" (MyNewtype 1)

nestedNewtypeMatch :: CompiledCode (MyNewtype2 -> Integer)
nestedNewtypeMatch = plc @"nestedNewtypeMatch" (\(MyNewtype2 (MyNewtype x)) -> x)

newtype ParamNewtype a = ParamNewtype (Maybe a)

paramNewtype :: CompiledCode (ParamNewtype Integer -> ParamNewtype Integer)
paramNewtype = plc @"paramNewtype" (\(x ::ParamNewtype Integer) -> x)

recursiveTypes :: TestNested
recursiveTypes = testNested "recursive" [
    goldenPir "listConstruct" listConstruct
    , goldenPir "listConstruct2" listConstruct2
    , goldenPir "listConstruct3" listConstruct3
    , goldenPir "listMatch" listMatch
    , goldenEval "listConstDest" [ getProgram listMatch, getProgram listConstruct ]
    , goldenEval "listConstDest2" [ getProgram listMatch, getProgram listConstruct2 ]
    , goldenPir "ptreeConstruct" ptreeConstruct
    , goldenPir "ptreeMatch" ptreeMatch
    , goldenEval "ptreeConstDest" [ getProgram ptreeMatch, getProgram ptreeConstruct ]
    , goldenEval "polyRecEval" [ getProgram polyRec, getProgram ptreeConstruct ]
    , goldenEval "ptreeFirstEval" [ getProgram ptreeFirst, getProgram ptreeConstruct ]
    , goldenEval "sameEmptyRoseEval" [ getProgram sameEmptyRose, getProgram emptyRoseConstruct ]
    , goldenPlc "sameEmptyRose" sameEmptyRose
  ]

listConstruct :: CompiledCode [Integer]
listConstruct = plc @"listConstruct" ([]::[Integer])

-- This will generate code using 'build' if we're on greater than -O0. That's not optimal for
-- us, since we don't have any rewrite rules to fire, but it's fine and we can handle it.
listConstruct2 :: CompiledCode [Integer]
listConstruct2 = plc @"listConstruct2" ([1]::[Integer])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode [Integer]
listConstruct3 = plc @"listConstruct3" ((1::Integer):(2::Integer):(3::Integer):[])

listMatch :: CompiledCode ([Integer] -> Integer)
listMatch = plc @"listMatch" (\(l::[Integer]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode (B Integer)
ptreeConstruct = plc @"ptreeConstruct" (Two (Two (One ((1,2),(3,4)))) :: B Integer)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode (B Integer -> Integer)
ptreeMatch = plc @"ptreeMatch" (\(t::B Integer) -> case t of { One a -> a; Two _ -> 2; })

polyRec :: CompiledCode (B Integer -> Integer)
polyRec = plc @"polyRec" (
    let
        depth :: B a -> Integer
        depth tree = case tree of
            One _     -> 1
            Two inner -> Builtins.addInteger 1 (depth inner)
    in \(t::B Integer) -> depth t)

ptreeFirst :: CompiledCode (B Integer -> Integer)
ptreeFirst = plc @"ptreeFirst" (
    let go :: (a -> Integer) -> B a -> Integer
        go k (One x) = k x
        go k (Two b) = go (\(x, _) -> k x) b
    in go (\x -> x))

data EmptyRose = EmptyRose [EmptyRose]

emptyRoseConstruct :: CompiledCode EmptyRose
emptyRoseConstruct = plc @"emptyRoseConstruct" (EmptyRose [EmptyRose [], EmptyRose []])

sameEmptyRose :: CompiledCode (EmptyRose -> EmptyRose)
sameEmptyRose = plc @"sameEmptyRose" (
    -- The type signatures are needed due to a bug (see 'emptyRoseNewId')
    let (.|) :: ([EmptyRose] -> [EmptyRose]) -> (EmptyRose -> [EmptyRose]) -> EmptyRose -> [EmptyRose]
        (.|) = \g f x -> g (f x)
        (|.) :: ([EmptyRose] -> EmptyRose) -> (EmptyRose -> [EmptyRose]) -> EmptyRose -> EmptyRose
        (|.) = \g f x -> g (f x)
        map :: (EmptyRose -> EmptyRose) -> [EmptyRose] -> [EmptyRose]
        map _ []     = []
        map f (x:xs) = f x : map f xs
        unEmptyRose (EmptyRose x) = x
        go = EmptyRose |. (map go .| unEmptyRose)
    in go)
