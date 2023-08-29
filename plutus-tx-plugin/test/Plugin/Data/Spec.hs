-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NegativeLiterals    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Plugin.Data.Spec where

import Test.Tasty.Extras

import PlutusCore.Pretty qualified as PLC
import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

import Data.Proxy

datat :: TestNested
datat = testNestedGhc "Data" [
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
  , goldenPir "monoCaseStrict" monoCaseStrict
  , goldenUEval "monoConstDest" [ toUPlc monoCase, toUPlc monoConstructed ]
  , goldenPir "defaultCase" defaultCase
  , goldenPir "irrefutableMatch" irrefutableMatch
  , goldenPir "atPattern" atPattern
  , goldenUEval "monoConstDestDefault" [ toUPlc monoCase, toUPlc monoConstructed ]
  , goldenPir "monoRecord" monoRecord
  , goldenPir "recordNewtype" recordNewtype
  , goldenPir "recordWithStrictField" recordWithStrictField
  , goldenPir "unusedWrapper" unusedWrapper
  , goldenPir "nonValueCase" nonValueCase
  , goldenPir "strictDataMatch" strictDataMatch
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode MyEnum
basicEnum = plc (Proxy @"basicEnum") Enum1

data MyMonoData = Mono1 Integer Integer | Mono2 Integer | Mono3 Integer
    deriving stock (Show, Eq)

instance P.Eq MyMonoData where
    {-# INLINABLE (==) #-}
    (Mono1 i1 j1) == (Mono1 i2 j2) = i1 P.== i2 && j1 P.== j2
    (Mono2 i1) == (Mono2 i2)       = i1 P.== i2
    (Mono3 i1) == (Mono3 i2)       = i1 P.== i2
    _ == _                         = False

-- pattern match to avoid type getting simplified away
monoDataType :: CompiledCode (MyMonoData -> Integer)
monoDataType = plc (Proxy @"monoDataType") (\(x :: MyMonoData) -> case x of { Mono2 i -> i; _ -> 1; })

{-
This is one of the test cases that reveals a bug in GHC 9: it fails to perform some
eta reductions that should be performed.

The CoreExpr for this test case in GHC 8 is simply @Mono1@, but in GHC 9, it becomes
@\ds1 ds2 -> Mono1 ds1 ds2@. This leads to bigger PIR, since we don't do eta reduction in PIR.

The reason for the GHC 9 behavior appears to be this Multiplicity check:
https://gitlab.haskell.org/ghc/ghc/-/blob/a54827e0b48af33fa9cfde6ad131c6751c2fe321/compiler/GHC/Core/Utils.hs#L2501.
GHC thinks @Mono1@ has a linear type, but @ds1@ and @ds2@ are non-linear, and the check is False.

The GHC 8 behavior is restored if @MyMonoData@ is defined this way:

@
data MyMonoData where
  Mono1 :: Integer %Many -> Integer %Many -> MyMonoData
  Mono2 :: Integer %Many -> MyMonoData
  Mono3 :: Integer %Many -> MyMonoData
@
-}
monoConstructor :: CompiledCode (Integer -> Integer -> MyMonoData)
monoConstructor = plc (Proxy @"monoConstructor") Mono1

monoConstructed :: CompiledCode MyMonoData
monoConstructed = plc (Proxy @"monoConstructed") (Mono2 1)

monoCase :: CompiledCode (MyMonoData -> Integer)
monoCase = plc (Proxy @"monoCase") (\(x :: MyMonoData) -> case x of { Mono1 _ b -> b;  Mono2 a -> a; Mono3 a -> a })

-- Bang patterns on pattern-matches do nothing: it's already strict
monoCaseStrict :: CompiledCode (MyMonoData -> Integer)
monoCaseStrict = plc (Proxy @"monoCase") (\(x :: MyMonoData) -> case x of { Mono1 _ !b -> b;  Mono2 a -> a; Mono3 !a -> a })

defaultCase :: CompiledCode (MyMonoData -> Integer)
defaultCase = plc (Proxy @"defaultCase") (\(x :: MyMonoData) -> case x of { Mono3 a -> a ; _ -> 2; })

irrefutableMatch :: CompiledCode (MyMonoData -> Integer)
irrefutableMatch = plc (Proxy @"irrefutableMatch") (\(x :: MyMonoData) -> case x of { Mono2 a -> a })

atPattern :: CompiledCode ((Integer, Integer) -> Integer)
atPattern = plc (Proxy @"atPattern") (\t@(_::Integer, y::Integer) -> let fst (a, _) = a in Builtins.addInteger y (fst t))

data MyMonoRecord = MyMonoRecord { mrA :: Integer , mrB :: Integer}
    deriving stock (Show, Eq)

instance P.Eq MyMonoRecord where
    {-# INLINABLE (==) #-}
    (MyMonoRecord i1 j1) == (MyMonoRecord i2 j2) = i1 P.== i2 && j1 P.== j2

-- pattern match to avoid type getting simplified away
monoRecord :: CompiledCode (MyMonoRecord -> Integer)
monoRecord = plc (Proxy @"monoRecord") (\(x :: MyMonoRecord) -> case x of { MyMonoRecord i _ -> i; })

data RecordNewtype = RecordNewtype { newtypeField :: MyNewtype }

-- pattern match to avoid type getting simplified away
recordNewtype :: CompiledCode (RecordNewtype -> Integer)
recordNewtype = plc (Proxy @"recordNewtype") (\(x :: RecordNewtype) -> case x of { RecordNewtype (MyNewtype i) -> i; })

data RecordWithStrictField = RecordWithStrictField { strictField1 :: !MyMonoRecord, strictField2 :: !RecordNewtype }

-- checks that the type of 'strictField2' is replaced with 'Integer', see Note [On data constructor workers and wrappers]
recordWithStrictField :: CompiledCode (RecordWithStrictField -> RecordNewtype)
recordWithStrictField = plc (Proxy @"recordWithStrictField") (\(x :: RecordWithStrictField) -> strictField2 x)

data T = MkT !(Integer,Integer)

mkT :: (Integer, Integer) -> T
mkT = MkT

-- checks that the 'wrapper' is compiled but unused, see Note [On data constructor workers and wrappers]
unusedWrapper :: CompiledCode T
unusedWrapper = plc (Proxy @"unusedWrapper") ((\x (y, z) -> x (z, y)) mkT (1, 2))

-- must be compiled with a lazy case
nonValueCase :: CompiledCode (MyEnum -> Integer)
nonValueCase = plc (Proxy @"nonValueCase") (\(x :: MyEnum) -> case x of { Enum1 -> 1::Integer ; Enum2 -> Builtins.error (); })

-- Bang patterns on data types do nothing: fields are already strict
data StrictTy a = StrictTy !a !a

strictDataMatch :: CompiledCode (StrictTy Integer)
strictDataMatch = plc (Proxy @"strictDataMatch") (StrictTy 1 2)

type Synonym = Integer

synonym :: CompiledCode Integer
synonym = plc (Proxy @"synonym") (1::Synonym)

polyData :: TestNested
polyData = testNested "polymorphic" [
    goldenPir "polyDataType" polyDataType
  , goldenPir "polyConstructed" polyConstructed
  , goldenPir "defaultCasePoly" defaultCasePoly
  ]

data MyPolyData a b = Poly1 a b | Poly2 a

instance (P.Eq a, P.Eq b) => P.Eq (MyPolyData a b) where
    {-# INLINABLE (==) #-}
    (Poly1 a1 b1) == (Poly1 a2 b2) = a1 P.== a2 && b1 P.== b2
    (Poly2 a1) == (Poly2 a2)       = a1 P.== a2
    _ == _                         = False

-- pattern match to avoid type getting simplified away
polyDataType :: CompiledCode (MyPolyData Integer Integer -> Integer)
polyDataType = plc (Proxy @"polyDataType") (\(x:: MyPolyData Integer Integer) -> case x of { Poly2 i -> i; _ -> 1; })

polyConstructed :: CompiledCode (MyPolyData Integer Integer)
polyConstructed = plc (Proxy @"polyConstructed") (Poly1 (1::Integer) (2::Integer))

defaultCasePoly :: CompiledCode (MyPolyData Integer Integer -> Integer)
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
    deriving stock (Show, Eq)

newtype MyNewtype2 = MyNewtype2 MyNewtype

basicNewtype :: CompiledCode (MyNewtype -> MyNewtype)
basicNewtype = plc (Proxy @"basicNewtype") (\(x::MyNewtype) -> x)

newtypeMatch :: CompiledCode (MyNewtype -> Integer)
newtypeMatch = plc (Proxy @"newtypeMatch") (\(MyNewtype x) -> x)

newtypeCreate :: CompiledCode (Integer -> MyNewtype)
newtypeCreate = plc (Proxy @"newtypeCreate") (\(x::Integer) -> MyNewtype x)

newtypeId :: CompiledCode (MyNewtype -> MyNewtype)
newtypeId = plc (Proxy @"newtypeId") (\(MyNewtype x) -> MyNewtype x)

newtypeCreate2 :: CompiledCode MyNewtype
newtypeCreate2 = plc (Proxy @"newtypeCreate2") (MyNewtype 1)

nestedNewtypeMatch :: CompiledCode (MyNewtype2 -> Integer)
nestedNewtypeMatch = plc (Proxy @"nestedNewtypeMatch") (\(MyNewtype2 (MyNewtype x)) -> x)

newtype ParamNewtype a = ParamNewtype (Maybe a)

-- pattern match to avoid type getting simplified away
paramNewtype :: CompiledCode (ParamNewtype Integer -> Integer)
paramNewtype = plc (Proxy @"paramNewtype") (\(x ::ParamNewtype Integer) -> case x of { ParamNewtype (Just i) -> i; _ -> 1 })

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
    , goldenTPlcWith
        ".tplc-read"
        (ppThrow . fmap PLC.AsReadable)
        "interListConstruct"
        interListConstruct
    , goldenUEval "processInterListEval" [ toUPlc processInterList, toUPlc interListConstruct ]
  ]

listConstruct :: CompiledCode [Integer]
listConstruct = plc (Proxy @"listConstruct") ([]::[Integer])

-- This will generate code using 'build' if we're on greater than -O0. That's not optimal for
-- us, since we don't have any rewrite rules to fire, but it's fine and we can handle it.
listConstruct2 :: CompiledCode [Integer]
listConstruct2 = plc (Proxy @"listConstruct2") ([1]::[Integer])

-- It is very difficult to get GHC to make a non-polymorphic redex if you use
-- list literal syntax with integers. But this works.
listConstruct3 :: CompiledCode [Integer]
listConstruct3 = plc (Proxy @"listConstruct3") ((1::Integer):(2::Integer):(3::Integer):[])

listMatch :: CompiledCode ([Integer] -> Integer)
listMatch = plc (Proxy @"listMatch") (\(l::[Integer]) -> case l of { (x:_) -> x ; [] -> 0; })

{- Note [Non-regular data types in tests]
A non-regular data type, a.k.a. a nested data type is, quoting "Nested Datatypes" by Richard Bird
and Lambert Meertens, a parametrised data type whose declaration involves different instances of the
accompanying type parameters. Such data types cannot be encoded with regular @fix :: (* -> *) -> *@
and require our fancy @ifix@ business, hence they make for good tests, which is how we have so many
of them.
-}

-- See Note [Non-regular data types in tests].
-- | A type of perfectly balanced binary trees.
data B a = One a | Two (B (a, a))

ptreeConstruct :: CompiledCode (B Integer)
ptreeConstruct = plc (Proxy @"ptreeConstruct") (Two (Two (One ((1,2),(3,4)))) :: B Integer)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: CompiledCode (B Integer -> Integer)
ptreeMatch = plc (Proxy @"ptreeMatch") (\(t::B Integer) -> case t of { One a -> a; Two _ -> 2; })

polyRec :: CompiledCode (B Integer -> Integer)
polyRec = plc (Proxy @"polyRec") (
    let
        depth :: B a -> Integer
        depth tree = case tree of
            One _     -> 1
            Two inner -> Builtins.addInteger 1 (depth inner)
    in \(t::B Integer) -> depth t)

ptreeFirst :: CompiledCode (B Integer -> Integer)
ptreeFirst = plc (Proxy @"ptreeFirst") (
    let go :: (a -> Integer) -> B a -> Integer
        go k (One x) = k x
        go k (Two b) = go (\(x, _) -> k x) b
    in go (\x -> x))

-- See Note [Non-regular data types in tests].
-- | A type of rose trees with empty leaves.
data EmptyRose = EmptyRose [EmptyRose]

emptyRoseConstruct :: CompiledCode EmptyRose
emptyRoseConstruct = plc (Proxy @"emptyRoseConstruct") (EmptyRose [EmptyRose [], EmptyRose []])

sameEmptyRose :: CompiledCode (EmptyRose -> EmptyRose)
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

-- See Note [Non-regular data types in tests].
-- | A type of lists containing two values at each node, with the types of those values getting
-- swapped each time we move from one node to the next one.
data InterList a b
    = InterNil
    | InterCons a b (InterList b a)  -- Note that the parameters get swapped.

interListConstruct :: CompiledCode (InterList Integer Bool)
interListConstruct =
    plc
        (Proxy @"interListConstruct")
        (InterCons 0 False (InterCons False (-1) (InterCons 42 True InterNil)))

processInterList :: CompiledCode (InterList Integer Bool -> Integer)
processInterList = plc (Proxy @"foldrInterList") (
    let foldrInterList :: forall a b r. (a -> b -> r -> r) -> r -> InterList a b -> r
        foldrInterList f0 z = go f0 where
          go :: forall a b. (a -> b -> r -> r) -> InterList a b -> r
          go _  InterNil          = z
          go f (InterCons x y xs) = f x y (go (flip f) xs)
    in foldrInterList (\x b r -> if b then x else r) 0)

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

basicClosed :: CompiledCode (BasicClosed Bool -> BasicClosed Bool)
basicClosed = plc (Proxy @"basicClosed") (\(x :: BasicClosed Bool) -> x)

type family BasicOpen a
type instance BasicOpen Bool = Integer

basicOpen :: CompiledCode (BasicOpen Bool -> BasicOpen Bool)
basicOpen = plc (Proxy @"basicOpen") (\(x :: BasicOpen Bool) -> x)

class Associated a where
    type AType a

instance Associated Bool where
    type instance AType Bool = Integer

data Param a = Param a

instance Associated (Param a) where
    type instance AType (Param a) = a

associated :: CompiledCode (AType Bool -> AType Bool)
associated = plc (Proxy @"associated") (\(x :: AType Bool) -> x)

-- Despite the type family being applied to a parameterized type we can still reduce it
{-# NOINLINE paramId #-}
paramId :: forall a . Param a -> AType (Param a) -> AType (Param a)
paramId _ x = x

associatedParam :: CompiledCode Integer
associatedParam = plc (Proxy @"associatedParam") (paramId (Param 1) 1)

-- Here we cannot reduce the type family
{-# NOINLINE tfId #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
tfId :: forall a . a -> BasicClosed a -> BasicClosed a
tfId _ x = x

irreducible :: CompiledCode Integer
irreducible = plc (Proxy @"irreducible") (tfId True 1)

data family BasicData a
data instance BasicData Bool = Inst Integer

basicData :: CompiledCode (BasicData Bool -> Integer)
basicData = plc (Proxy @"basicData") (\(x :: BasicData Bool) -> let Inst i = x in i)
