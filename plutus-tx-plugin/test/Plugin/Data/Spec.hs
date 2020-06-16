{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Data.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore.Universe as PLC

import           Data.Proxy

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

datat :: TestNested
datat = testNested "Data" [
    monoData
  , polyData
  , newtypes
  , recursiveTypes
  , typeFamilies
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
  , goldenPir "strictPattern" strictPattern
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode PLC.DefaultUni MyEnum
basicEnum = plc (Proxy @"basicEnum") Enum1

data MyMonoData = Mono1 Integer Integer | Mono2 Integer | Mono3 Integer
    deriving (Show, Eq)

monoDataType :: CompiledCode PLC.DefaultUni (MyMonoData -> MyMonoData)
monoDataType = plc (Proxy @"monoDataType") (\(x :: MyMonoData) -> x)

monoConstructor :: CompiledCode PLC.DefaultUni (Integer -> Integer -> MyMonoData)
monoConstructor = plc (Proxy @"monConstructor") Mono1

monoConstructed :: CompiledCode PLC.DefaultUni MyMonoData
monoConstructed = plc (Proxy @"monoConstructed") (Mono2 1)

monoCase :: CompiledCode PLC.DefaultUni (MyMonoData -> Integer)
monoCase = plc (Proxy @"monoCase") (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: CompiledCode PLC.DefaultUni (MyMonoData -> Integer)
defaultCase = plc (Proxy @"defaultCase") (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: CompiledCode PLC.DefaultUni (MyMonoData -> Integer)
irrefutableMatch = plc (Proxy @"irrefutableMatch") (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

atPattern :: CompiledCode PLC.DefaultUni ((Integer, Integer) -> Integer)
atPattern = plc (Proxy @"atPattern") (\t@(x::Integer, y::Integer) -> let fst (a, b) = a in Builtins.addInteger y (fst t))

data MyMonoRecord = MyMonoRecord { mrA :: Integer , mrB :: Integer}
    deriving (Show, Eq)

monoRecord :: CompiledCode PLC.DefaultUni (MyMonoRecord -> MyMonoRecord)
monoRecord = plc (Proxy @"monoRecord") (\(x :: MyMonoRecord) -> x)

data RecordNewtype = RecordNewtype { newtypeField :: MyNewtype }

recordNewtype :: CompiledCode PLC.DefaultUni (RecordNewtype -> RecordNewtype)
recordNewtype = plc (Proxy @"recordNewtype") (\(x :: RecordNewtype) -> x)

-- must be compiled with a lazy case
nonValueCase :: CompiledCode PLC.DefaultUni (MyEnum -> Integer)
nonValueCase = plc (Proxy @"nonValueCase") (\(x :: MyEnum) -> case x of { Enum1 -> 1::Integer ; Enum2 -> Builtins.error (); })

data StrictPattern a = StrictPattern !a !a

strictPattern :: CompiledCode PLC.DefaultUni (StrictPattern Integer)
strictPattern = plc (Proxy @"strictPattern") (StrictPattern 1 2)

type Synonym = Integer

synonym :: CompiledCode PLC.DefaultUni Integer
synonym = plc (Proxy @"synonym") (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPir "polyDataType" polyDataType
  , goldenPir "polyConstructed" polyConstructed
  , goldenPir "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: CompiledCode PLC.DefaultUni (MyPolyData Integer Integer -> MyPolyData Integer Integer)
polyDataType = plc (Proxy @"polyDataType") (\(x:: MyPolyData Integer Integer) -> x)

polyConstructed :: CompiledCode PLC.DefaultUni (MyPolyData Integer Integer)
polyConstructed = plc (Proxy @"polyConstructed") (Poly1 (1::Integer) (2::Integer))

defaultCasePoly :: CompiledCode PLC.DefaultUni (MyPolyData Integer Integer -> Integer)
defaultCasePoly = plc (Proxy @"defaultCasePoly") (\(x :: MyPolyData Integer Integer) -> case x of { Poly1 a _ -> a ; _ -> 2; })

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

basicNewtype :: CompiledCode PLC.DefaultUni (MyNewtype -> MyNewtype)
basicNewtype = plc (Proxy @"basicNewtype") (\(x::MyNewtype) -> x)

newtypeMatch :: CompiledCode PLC.DefaultUni (MyNewtype -> Integer)
newtypeMatch = plc (Proxy @"newtypeMatch") (\(MyNewtype x) -> x)

newtypeCreate :: CompiledCode PLC.DefaultUni (Integer -> MyNewtype)
newtypeCreate = plc (Proxy @"newtypeCreate") (\(x::Integer) -> MyNewtype x)

newtypeId :: CompiledCode PLC.DefaultUni (MyNewtype -> MyNewtype)
newtypeId = plc (Proxy @"newtypeId") (\(MyNewtype x) -> MyNewtype x)

newtypeCreate2 :: CompiledCode PLC.DefaultUni MyNewtype
newtypeCreate2 = plc (Proxy @"newtypeCreate2") (MyNewtype 1)

nestedNewtypeMatch :: CompiledCode PLC.DefaultUni (MyNewtype2 -> Integer)
nestedNewtypeMatch = plc (Proxy @"nestedNewtypeMatch") (\(MyNewtype2 (MyNewtype x)) -> x)

newtype ParamNewtype a = ParamNewtype (Maybe a)

paramNewtype :: CompiledCode PLC.DefaultUni (ParamNewtype Integer -> ParamNewtype Integer)
paramNewtype = plc (Proxy @"paramNewtype") (\(x ::ParamNewtype Integer) -> x)

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

listConstruct :: CompiledCode PLC.DefaultUni [Integer]
listConstruct = plc (Proxy @"listConstruct") ([]::[Integer])

-- This will generate code using 'build' if we're on greater than -O0. That's not optimal for
-- us, since we don't have any rewrite rules to fire, but it's fine and we can handle it.
listConstruct2 :: CompiledCode PLC.DefaultUni [Integer]
listConstruct2 = plc (Proxy @"listConstruct2") ([1]::[Integer])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode PLC.DefaultUni [Integer]
listConstruct3 = plc (Proxy @"listConstruct3") ((1::Integer):(2::Integer):(3::Integer):[])

listMatch :: CompiledCode PLC.DefaultUni ([Integer] -> Integer)
listMatch = plc (Proxy @"listMatch") (\(l::[Integer]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode PLC.DefaultUni (B Integer)
ptreeConstruct = plc (Proxy @"ptreeConstruct") (Two (Two (One ((1,2),(3,4)))) :: B Integer)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode PLC.DefaultUni (B Integer -> Integer)
ptreeMatch = plc (Proxy @"ptreeMatch") (\(t::B Integer) -> case t of { One a -> a; Two _ -> 2; })

polyRec :: CompiledCode PLC.DefaultUni (B Integer -> Integer)
polyRec = plc (Proxy @"polyRec") (
    let
        depth :: B a -> Integer
        depth tree = case tree of
            One _     -> 1
            Two inner -> Builtins.addInteger 1 (depth inner)
    in \(t::B Integer) -> depth t)

ptreeFirst :: CompiledCode PLC.DefaultUni (B Integer -> Integer)
ptreeFirst = plc (Proxy @"ptreeFirst") (
    let go :: (a -> Integer) -> B a -> Integer
        go k (One x) = k x
        go k (Two b) = go (\(x, _) -> k x) b
    in go (\x -> x))

data EmptyRose = EmptyRose [EmptyRose]

emptyRoseConstruct :: CompiledCode PLC.DefaultUni EmptyRose
emptyRoseConstruct = plc (Proxy @"emptyRoseConstruct") (EmptyRose [EmptyRose [], EmptyRose []])

sameEmptyRose :: CompiledCode PLC.DefaultUni (EmptyRose -> EmptyRose)
sameEmptyRose = plc (Proxy @"sameEmptyRose") (
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

typeFamilies :: TestNested
typeFamilies = testNested "families" [
    goldenPir "basicClosed" basicClosed
    , goldenPir "basicOpen" basicOpen
    , goldenPir "associated" associated
    , goldenPir "associatedParam" associatedParam
    , goldenPir "basicData" basicData
    , goldenPlcCatch "irreducible" irreducible
  ]

type family BasicClosed a where
    BasicClosed Bool = Integer

basicClosed :: CompiledCode PLC.DefaultUni (BasicClosed Bool -> BasicClosed Bool)
basicClosed = plc (Proxy @"basicClosed") (\(x :: BasicClosed Bool) -> x)

type family BasicOpen a
type instance BasicOpen Bool = Integer

basicOpen :: CompiledCode PLC.DefaultUni (BasicOpen Bool -> BasicOpen Bool)
basicOpen = plc (Proxy @"basicOpen") (\(x :: BasicOpen Bool) -> x)

class Associated a where
    type AType a

instance Associated Bool where
    type instance AType Bool = Integer

data Param a = Param a

instance Associated (Param a) where
    type instance AType (Param a) = a

associated :: CompiledCode PLC.DefaultUni (AType Bool -> AType Bool)
associated = plc (Proxy @"associated") (\(x :: AType Bool) -> x)

-- Despite the type family being applied to a parameterized type we can still reduce it
{-# NOINLINE paramId #-}
paramId :: forall a . Param a -> AType (Param a) -> AType (Param a)
paramId _ x = x

associatedParam :: CompiledCode PLC.DefaultUni Integer
associatedParam = plc (Proxy @"associatedParam") (paramId (Param 1) 1)

-- Here we cannot reduce the type family
{-# NOINLINE tfId #-}
tfId :: forall a . a -> BasicClosed a -> BasicClosed a
tfId _ x = x

irreducible :: CompiledCode PLC.DefaultUni Integer
irreducible = plc (Proxy @"irreducible") (tfId True 1)

data family BasicData a
data instance BasicData Bool = Inst Integer

basicData :: CompiledCode PLC.DefaultUni (BasicData Bool -> Integer)
basicData = plc (Proxy @"basicData") (\(x :: BasicData Bool) -> let Inst i = x in i)
