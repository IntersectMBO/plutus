{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Data.Spec where

import           Common
import           PlcTestUtils
import           Lib
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore.Universe as PLC
import qualified Language.PlutusCore.Builtins as PLC

import           Data.Proxy

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
  , goldenUEval "monoConstDest" [ toUPlc monoCase, toUPlc monoConstructed ]
  , goldenPir "defaultCase" defaultCase
  , goldenPir "irrefutableMatch" irrefutableMatch
  , goldenPir "atPattern" atPattern
  , goldenUEval "monoConstDestDefault" [ toUPlc monoCase, toUPlc monoConstructed ]
  , goldenPir "monoRecord" monoRecord
  , goldenPir "recordNewtype" recordNewtype
  , goldenPir "nonValueCase" nonValueCase
  , goldenPir "strictPattern" strictPattern
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode PLC.DefaultUni PLC.DefaultFun MyEnum
basicEnum = plc (Proxy @"basicEnum") Enum1

data MyMonoData = Mono1 Integer Integer | Mono2 Integer | Mono3 Integer
    deriving (Show, Eq)

monoDataType :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyMonoData -> MyMonoData)
monoDataType = plc (Proxy @"monoDataType") (\(x :: MyMonoData) -> x)

monoConstructor :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> MyMonoData)
monoConstructor = plc (Proxy @"monConstructor") Mono1

monoConstructed :: CompiledCode PLC.DefaultUni PLC.DefaultFun MyMonoData
monoConstructed = plc (Proxy @"monoConstructed") (Mono2 1)

monoCase :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyMonoData -> Integer)
monoCase = plc (Proxy @"monoCase") (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

defaultCase :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyMonoData -> Integer)
defaultCase = plc (Proxy @"defaultCase") (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyMonoData -> Integer)
irrefutableMatch = plc (Proxy @"irrefutableMatch") (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

atPattern :: CompiledCode PLC.DefaultUni PLC.DefaultFun ((Integer, Integer) -> Integer)
atPattern = plc (Proxy @"atPattern") (\t@(x::Integer, y::Integer) -> let fst (a, b) = a in Builtins.addInteger y (fst t))

data MyMonoRecord = MyMonoRecord { mrA :: Integer , mrB :: Integer}
    deriving (Show, Eq)

monoRecord :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyMonoRecord -> MyMonoRecord)
monoRecord = plc (Proxy @"monoRecord") (\(x :: MyMonoRecord) -> x)

data RecordNewtype = RecordNewtype { newtypeField :: MyNewtype }

recordNewtype :: CompiledCode PLC.DefaultUni PLC.DefaultFun (RecordNewtype -> RecordNewtype)
recordNewtype = plc (Proxy @"recordNewtype") (\(x :: RecordNewtype) -> x)

-- must be compiled with a lazy case
nonValueCase :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyEnum -> Integer)
nonValueCase = plc (Proxy @"nonValueCase") (\(x :: MyEnum) -> case x of { Enum1 -> 1::Integer ; Enum2 -> Builtins.error (); })

data StrictPattern a = StrictPattern !a !a

strictPattern :: CompiledCode PLC.DefaultUni PLC.DefaultFun (StrictPattern Integer)
strictPattern = plc (Proxy @"strictPattern") (StrictPattern 1 2)

type Synonym = Integer

synonym :: CompiledCode PLC.DefaultUni PLC.DefaultFun Integer
synonym = plc (Proxy @"synonym") (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPir "polyDataType" polyDataType
  , goldenPir "polyConstructed" polyConstructed
  , goldenPir "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

polyDataType :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyPolyData Integer Integer -> MyPolyData Integer Integer)
polyDataType = plc (Proxy @"polyDataType") (\(x:: MyPolyData Integer Integer) -> x)

polyConstructed :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyPolyData Integer Integer)
polyConstructed = plc (Proxy @"polyConstructed") (Poly1 (1::Integer) (2::Integer))

defaultCasePoly :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyPolyData Integer Integer -> Integer)
defaultCasePoly = plc (Proxy @"defaultCasePoly") (\(x :: MyPolyData Integer Integer) -> case x of { Poly1 a _ -> a ; _ -> 2; })

newtypes :: TestNested
newtypes = testNested "newtypes" [
    goldenPir "basicNewtype" basicNewtype
   , goldenPir "newtypeMatch" newtypeMatch
   , goldenPir "newtypeCreate" newtypeCreate
   , goldenPir "newtypeId" newtypeId
   , goldenPir "newtypeCreate2" newtypeCreate2
   , goldenPir "nestedNewtypeMatch" nestedNewtypeMatch
   , goldenUEval "newtypeCreatDest" [ toUPlc $ newtypeMatch, toUPlc $ newtypeCreate2 ]
   , goldenPir "paramNewtype" paramNewtype
   ]

newtype MyNewtype = MyNewtype Integer
    deriving (Show, Eq)

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyNewtype -> MyNewtype)
basicNewtype = plc (Proxy @"basicNewtype") (\(x::MyNewtype) -> x)

newtypeMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyNewtype -> Integer)
newtypeMatch = plc (Proxy @"newtypeMatch") (\(MyNewtype x) -> x)

newtypeCreate :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> MyNewtype)
newtypeCreate = plc (Proxy @"newtypeCreate") (\(x::Integer) -> MyNewtype x)

newtypeId :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyNewtype -> MyNewtype)
newtypeId = plc (Proxy @"newtypeId") (\(MyNewtype x) -> MyNewtype x)

newtypeCreate2 :: CompiledCode PLC.DefaultUni PLC.DefaultFun MyNewtype
newtypeCreate2 = plc (Proxy @"newtypeCreate2") (MyNewtype 1)

nestedNewtypeMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun (MyNewtype2 -> Integer)
nestedNewtypeMatch = plc (Proxy @"nestedNewtypeMatch") (\(MyNewtype2 (MyNewtype x)) -> x)

newtype ParamNewtype a = ParamNewtype (Maybe a)

paramNewtype :: CompiledCode PLC.DefaultUni PLC.DefaultFun (ParamNewtype Integer -> ParamNewtype Integer)
paramNewtype = plc (Proxy @"paramNewtype") (\(x ::ParamNewtype Integer) -> x)

recursiveTypes :: TestNested
recursiveTypes = testNested "recursive" [
    goldenPir "listConstruct" listConstruct
    , goldenPir "listConstruct2" listConstruct2
    , goldenPir "listConstruct3" listConstruct3
    , goldenPir "listMatch" listMatch
    , goldenUEval "listConstDest" [ toUPlc listMatch, toUPlc listConstruct ]
    , goldenUEval "listConstDest2" [ toUPlc listMatch, toUPlc listConstruct2 ]
    , goldenPir "ptreeConstruct" ptreeConstruct
    , goldenPir "ptreeMatch" ptreeMatch
    , goldenUEval "ptreeConstDest" [ toUPlc ptreeMatch, toUPlc ptreeConstruct ]
    , goldenUEval "polyRecEval" [ toUPlc polyRec, toUPlc ptreeConstruct ]
    , goldenUEval "ptreeFirstEval" [ toUPlc ptreeFirst, toUPlc ptreeConstruct ]
    , goldenUEval "sameEmptyRoseEval" [ toUPlc sameEmptyRose, toUPlc emptyRoseConstruct ]
    , goldenUPlc "sameEmptyRose" sameEmptyRose
  ]

listConstruct :: CompiledCode PLC.DefaultUni PLC.DefaultFun [Integer]
listConstruct = plc (Proxy @"listConstruct") ([]::[Integer])

-- This will generate code using 'build' if we're on greater than -O0. That's not optimal for
-- us, since we don't have any rewrite rules to fire, but it's fine and we can handle it.
listConstruct2 :: CompiledCode PLC.DefaultUni PLC.DefaultFun [Integer]
listConstruct2 = plc (Proxy @"listConstruct2") ([1]::[Integer])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode PLC.DefaultUni PLC.DefaultFun [Integer]
listConstruct3 = plc (Proxy @"listConstruct3") ((1::Integer):(2::Integer):(3::Integer):[])

listMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun ([Integer] -> Integer)
listMatch = plc (Proxy @"listMatch") (\(l::[Integer]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode PLC.DefaultUni PLC.DefaultFun (B Integer)
ptreeConstruct = plc (Proxy @"ptreeConstruct") (Two (Two (One ((1,2),(3,4)))) :: B Integer)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun (B Integer -> Integer)
ptreeMatch = plc (Proxy @"ptreeMatch") (\(t::B Integer) -> case t of { One a -> a; Two _ -> 2; })

polyRec :: CompiledCode PLC.DefaultUni PLC.DefaultFun (B Integer -> Integer)
polyRec = plc (Proxy @"polyRec") (
    let
        depth :: B a -> Integer
        depth tree = case tree of
            One _     -> 1
            Two inner -> Builtins.addInteger 1 (depth inner)
    in \(t::B Integer) -> depth t)

ptreeFirst :: CompiledCode PLC.DefaultUni PLC.DefaultFun (B Integer -> Integer)
ptreeFirst = plc (Proxy @"ptreeFirst") (
    let go :: (a -> Integer) -> B a -> Integer
        go k (One x) = k x
        go k (Two b) = go (\(x, _) -> k x) b
    in go (\x -> x))

data EmptyRose = EmptyRose [EmptyRose]

emptyRoseConstruct :: CompiledCode PLC.DefaultUni PLC.DefaultFun EmptyRose
emptyRoseConstruct = plc (Proxy @"emptyRoseConstruct") (EmptyRose [EmptyRose [], EmptyRose []])

sameEmptyRose :: CompiledCode PLC.DefaultUni PLC.DefaultFun (EmptyRose -> EmptyRose)
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
    , goldenUPlcCatch "irreducible" irreducible
  ]

type family BasicClosed a where
    BasicClosed Bool = Integer

basicClosed :: CompiledCode PLC.DefaultUni PLC.DefaultFun (BasicClosed Bool -> BasicClosed Bool)
basicClosed = plc (Proxy @"basicClosed") (\(x :: BasicClosed Bool) -> x)

type family BasicOpen a
type instance BasicOpen Bool = Integer

basicOpen :: CompiledCode PLC.DefaultUni PLC.DefaultFun (BasicOpen Bool -> BasicOpen Bool)
basicOpen = plc (Proxy @"basicOpen") (\(x :: BasicOpen Bool) -> x)

class Associated a where
    type AType a

instance Associated Bool where
    type instance AType Bool = Integer

data Param a = Param a

instance Associated (Param a) where
    type instance AType (Param a) = a

associated :: CompiledCode PLC.DefaultUni PLC.DefaultFun (AType Bool -> AType Bool)
associated = plc (Proxy @"associated") (\(x :: AType Bool) -> x)

-- Despite the type family being applied to a parameterized type we can still reduce it
{-# NOINLINE paramId #-}
paramId :: forall a . Param a -> AType (Param a) -> AType (Param a)
paramId _ x = x

associatedParam :: CompiledCode PLC.DefaultUni PLC.DefaultFun Integer
associatedParam = plc (Proxy @"associatedParam") (paramId (Param 1) 1)

-- Here we cannot reduce the type family
{-# NOINLINE tfId #-}
tfId :: forall a . a -> BasicClosed a -> BasicClosed a
tfId _ x = x

irreducible :: CompiledCode PLC.DefaultUni PLC.DefaultFun Integer
irreducible = plc (Proxy @"irreducible") (tfId True 1)

data family BasicData a
data instance BasicData Bool = Inst Integer

basicData :: CompiledCode PLC.DefaultUni PLC.DefaultFun (BasicData Bool -> Integer)
basicData = plc (Proxy @"basicData") (\(x :: BasicData Bool) -> let Inst i = x in i)
