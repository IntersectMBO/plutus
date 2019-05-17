{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
-- this adds source notes which helps the plugin give better errors
{-# OPTIONS_GHC   -g #-}

module Plugin.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib
import           Plugin.ReadValue

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Lift
import           Language.PlutusTx.Plugin

import           Data.ByteString.Lazy       ()
import           Data.Text.Prettyprint.Doc

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
  , pure readDyns
  , unfoldings
  , laziness
  , errors
  , wobbly
  ]

basic :: TestNested
basic = testNested "basic" [
    goldenPir "monoId" monoId
  , goldenPir "monoK" monoK
  ]

monoId :: CompiledCode (Integer -> Integer)
monoId = plc @"monoId" (\(x :: Integer) -> x)

monoK :: CompiledCode (Integer -> Integer -> Integer)
monoK = plc @"monoK" (\(i :: Integer) -> \(j :: Integer) -> i)

primitives :: TestNested
primitives = testNested "primitives" [
    goldenPir "string" string
  , goldenPir "int" int
  , goldenPir "int2" int2
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
  , goldenPir "emptyByteString" emptyByteString
  , goldenEval "emptyByteStringApply" [ getPlc emptyByteString, unsafeLiftProgram (Builtins.emptyByteString) ]
  , goldenPir "bytestring" bytestring
  , goldenEval "bytestringApply" [ getPlc bytestring, unsafeLiftProgram ("hello"::Builtins.ByteString) ]
  , goldenEval "sha2_256" [ getPlc sha2, unsafeLiftProgram ("hello" :: Builtins.ByteString)]
  , goldenEval "equalsByteString" [ getPlc bsEquals, unsafeLiftProgram ("hello" :: Builtins.ByteString), unsafeLiftProgram ("hello" :: Builtins.ByteString)]
  , goldenPir "verify" verify
  , goldenPir "trace" trace
  ]

string :: CompiledCode String
string = plc @"string" "test"

int :: CompiledCode Integer
int = plc @"int" (1::Integer)

int2 :: CompiledCode Integer
int2 = plc @"int2" (2::Integer)

emptyBS :: CompiledCode (Builtins.ByteString)
emptyBS = plc @"emptyBS" (Builtins.emptyByteString)

bool :: CompiledCode Bool
bool = plc @"bool" True

andPlc :: CompiledCode (Bool -> Bool -> Bool)
andPlc = plc @"andPlc" (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode (Integer, Integer)
tuple = plc @"tuple" ((1::Integer), (2::Integer))

tupleMatch :: CompiledCode ((Integer, Integer) -> Integer)
tupleMatch = plc @"tupleMatch" (\(x:: (Integer, Integer)) -> let (a, b) = x in a)

intCompare :: CompiledCode (Integer -> Integer -> Bool)
intCompare = plc @"intCompare" (\(x::Integer) (y::Integer) -> Builtins.lessThanInteger x y)

intEq :: CompiledCode (Integer -> Integer -> Bool)
intEq = plc @"intEq" (\(x::Integer) (y::Integer) -> Builtins.equalsInteger x y)

-- Has a Void in it
void :: CompiledCode (Integer -> Integer -> Bool)
void = plc @"void" (\(x::Integer) (y::Integer) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in (Builtins.equalsInteger x y) `a` (Builtins.equalsInteger y x))

intPlus :: CompiledCode (Integer -> Integer -> Integer)
intPlus = plc @"intPlus" (\(x::Integer) (y::Integer) -> Builtins.addInteger x y)

intDiv :: CompiledCode (Integer -> Integer -> Integer)
intDiv = plc @"intDiv" (\(x::Integer) (y::Integer) -> Builtins.divideInteger x y)

errorPlc :: CompiledCode (() -> Integer)
errorPlc = plc @"errorPlc" (Builtins.error @Integer)

ifThenElse :: CompiledCode (Integer -> Integer -> Integer)
ifThenElse = plc @"ifThenElse" (\(x::Integer) (y::Integer) -> if Builtins.equalsInteger x y then x else y)

emptyByteString :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
emptyByteString = plc @"emptyByteString" (\(x :: Builtins.ByteString) -> x)

bytestring :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
bytestring = plc @"bytestring" (\(x::Builtins.ByteString) -> x)

sha2 :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
sha2 = plc @"sha2" (\(x :: Builtins.ByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsEquals = plc @"bs32Equals" (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.equalsByteString x y)

verify :: CompiledCode (Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString -> Bool)
verify = plc @"verify" (\(x::Builtins.ByteString) (y::Builtins.ByteString) (z::Builtins.ByteString) -> Builtins.verifySignature x y z)

trace :: CompiledCode (Builtins.String -> ())
trace = plc @"trace" (\(x :: Builtins.String) -> Builtins.trace x)

structure :: TestNested
structure = testNested "structure" [
    goldenPir "letFun" letFun
  ]

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun = plc @"lefFun" (\(x::Integer) (y::Integer) -> let f z = Builtins.equalsInteger x z in f y)

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
  , goldenPir "recordNewtype" recordNewtype
  , goldenPir "nonValueCase" nonValueCase
  , goldenPir "synonym" synonym
  ]

data MyEnum = Enum1 | Enum2

basicEnum :: CompiledCode MyEnum
basicEnum = plc @"basicEnum" (Enum1)

data MyMonoData = Mono1 Integer Integer | Mono2 Integer | Mono3 Integer
    deriving (Show, Eq)

monoDataType :: CompiledCode (MyMonoData -> MyMonoData)
monoDataType = plc @"monoDataType" (\(x :: MyMonoData) -> x)

monoConstructor :: CompiledCode (Integer -> Integer -> MyMonoData)
monoConstructor = plc @"monConstructor" (Mono1)

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
    , goldenEval "polyRecEval" [ getProgram $ polyRec, getProgram $ ptreeConstruct ]
    , goldenEval "ptreeFirstEval" [ getProgram $ ptreeFirst, getProgram $ ptreeConstruct ]
    , goldenEval "sameEmptyRoseEval" [ getProgram $ sameEmptyRose, getProgram $ emptyRoseConstruct ]
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

recursion :: TestNested
recursion = testNested "recursiveFunctions" [
    goldenPir "fib" fib
    , goldenEval "fib4" [ getProgram $ fib, getProgram $ plc @"4" (4::Integer) ]
    , goldenPir "sum" sumDirect
    , goldenEval "sumList" [ getProgram $ sumDirect, getProgram $ listConstruct3 ]
    , goldenPir "even" evenMutual
    , goldenEval "even3" [ getProgram $ evenMutual, getProgram $ plc @"3" (3::Integer) ]
    , goldenEval "even4" [ getProgram $ evenMutual, getProgram $ plc @"4" (4::Integer) ]
  ]

fib :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fib = plc @"fib" (
    let fib :: Integer -> Integer
        fib n = if Builtins.equalsInteger n 0
            then 0
            else if Builtins.equalsInteger n 1
            then 1
            else Builtins.addInteger (fib(Builtins.subtractInteger n 1)) (fib(Builtins.subtractInteger n 2))
    in fib)

sumDirect :: CompiledCode ([Integer] -> Integer)
sumDirect = plc @"sumDirect" (
    let sum :: [Integer] -> Integer
        sum []     = 0
        sum (x:xs) = Builtins.addInteger x (sum xs)
    in sum)

evenMutual :: CompiledCode (Integer -> Bool)
evenMutual = plc @"evenMutual" (
    let even :: Integer -> Bool
        even n = if Builtins.equalsInteger n 0 then True else odd (Builtins.subtractInteger n 1)
        odd :: Integer -> Bool
        odd n = if Builtins.equalsInteger n 0 then False else even (Builtins.subtractInteger n 1)
    in even)

unfoldings :: TestNested
unfoldings = testNested "unfoldings" [
    goldenPir "nandDirect" nandPlcDirect
    , goldenPir "andDirect" andPlcDirect
    , goldenPir "andExternal" andPlcExternal
    , goldenPir "allDirect" allPlcDirect
    , goldenPir "mutualRecursionUnfoldings" mutualRecursionUnfoldings
    , goldenPir "recordSelector" recordSelector
    , goldenPir "recordSelectorExternal" recordSelectorExternal
  ]

andDirect :: Bool -> Bool -> Bool
andDirect = \(a :: Bool) -> \(b::Bool) -> nandDirect (nandDirect a b) (nandDirect a b)

nandDirect :: Bool -> Bool -> Bool
nandDirect = \(a :: Bool) -> \(b::Bool) -> if a then False else if b then False else True

nandPlcDirect :: CompiledCode Bool
nandPlcDirect = plc @"nandPlcDirect" (nandDirect True False)

andPlcDirect :: CompiledCode Bool
andPlcDirect = plc @"andPlcDirect" (andDirect True False)

andPlcExternal :: CompiledCode Bool
andPlcExternal = plc @"andPlcExternal" (andExternal True False)

-- self-recursion
allDirect :: (a -> Bool) -> [a] -> Bool
allDirect p l = case l of
    []  -> True
    h:t -> andDirect (p h) (allDirect p t)

allPlcDirect :: CompiledCode Bool
allPlcDirect = plc @"andPlcDirect" (allDirect (\(x::Integer) -> Builtins.greaterThanInteger x 5) [7, 6])

mutualRecursionUnfoldings :: CompiledCode Bool
mutualRecursionUnfoldings = plc @"mutualRecursionUnfoldings" (evenDirect 4)

recordSelector :: CompiledCode (MyMonoRecord -> Integer)
recordSelector = plc @"recordSelector" (\(x :: MyMonoRecord) -> mrA x)

recordSelectorExternal :: CompiledCode (MyExternalRecord -> Integer)
recordSelectorExternal = plc @"recordSelectorExternal" (\(x :: MyExternalRecord) -> myExternal x)

laziness :: TestNested
laziness = testNested "laziness" [
    goldenPir "joinError" joinErrorPir
    , goldenEval "joinErrorEval" [ getProgram $ joinErrorPir, getProgram $ plc @"T" (True), getProgram $ plc @"F" (False)]
  ]

joinErrorPir :: CompiledCode (Bool -> Bool -> ())
joinErrorPir = plc @"joinError" joinError

errors :: TestNested
errors = testNested "errors" [
    goldenPlcCatch "machInt" machInt
    -- FIXME: This fails differently in nix, possibly due to slightly different optimization settings
    --, goldenPlcCatch "negativeInt" negativeInt
    , goldenPlcCatch "valueRestriction" valueRestriction
    , goldenPlcCatch "recursiveNewtype" recursiveNewtype
    , goldenPlcCatch "mutualRecursionUnfoldingsLocal" mutualRecursionUnfoldingsLocal
  ]

machInt :: CompiledCode Int
machInt = plc @"machInt" (1::Int)

negativeInt :: CompiledCode Integer
negativeInt = plc @"negativeInt" (-1 :: Integer)

-- It's little tricky to get something that GHC actually turns into a polymorphic computation! We use our value twice
-- at different types to prevent the obvious specialization.
valueRestriction :: CompiledCode (Bool, Integer)
valueRestriction = plc @"valueRestriction" (let { f :: forall a . a; f = Builtins.error (); } in (f @Bool, f @Integer))

newtype RecursiveNewtype = RecursiveNewtype [RecursiveNewtype]

recursiveNewtype :: CompiledCode (RecursiveNewtype)
recursiveNewtype = plc @"recursiveNewtype" (RecursiveNewtype [])

{-# INLINABLE evenDirectLocal #-}
evenDirectLocal :: Integer -> Bool
evenDirectLocal n = if Builtins.equalsInteger n 0 then True else oddDirectLocal (Builtins.subtractInteger n 1)

{-# INLINABLE oddDirectLocal #-}
oddDirectLocal :: Integer -> Bool
oddDirectLocal n = if Builtins.equalsInteger n 0 then False else evenDirectLocal (Builtins.subtractInteger n 1)

-- FIXME: these seem to only get unfoldings when they're in a separate module, even with the simplifier pass
mutualRecursionUnfoldingsLocal :: CompiledCode Bool
mutualRecursionUnfoldingsLocal = plc @"mutualRecursionUnfoldingsLocal" (evenDirectLocal 4)

wobbly :: TestNested
wobbly = testNested "wobbly" [
    -- We used to have problems with polymorphic let bindings where the generalization was
    -- on the outside of the let, which hit the value restriction. Now we hit the simplifier
    -- it seems to sometimes float these in, but we should keep an eye on these.
    goldenPir "emptyRoseId1" emptyRoseId1
    , goldenPir "polyMap" polyMap
  ]

emptyRoseId1 :: CompiledCode (EmptyRose -> EmptyRose)
emptyRoseId1 = plc @"emptyRoseId1" (
    let map _ []     = []
        map f (x:xs) = f x : map f xs
        go (EmptyRose xs) = EmptyRose (map go xs)
    in go)

mapDirect :: (a -> b) -> [a] -> [b]
mapDirect f l = case l of
    []   -> []
    x:xs -> f x : mapDirect f xs

polyMap :: CompiledCode ([Integer])
polyMap = plc @"polyMap" (mapDirect (Builtins.addInteger 1) [0, 1])

-- Unexpectedly results in
--
-- > Used but not defined in the current conversion: Variable EmptyRose
-- > [DataConWrapper]
-- emptyRoseId2 :: CompiledCode (EmptyRose -> EmptyRose)
-- emptyRoseId2 = plc @"emptyRoseId2" (
--     let (.) g f = \x -> g (f x)
--         unEmptyRose (EmptyRose xs) = xs
--     in EmptyRose . unEmptyRose)
