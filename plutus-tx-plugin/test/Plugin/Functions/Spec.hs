-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE UnboxedTuples       #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Plugin.Functions.Spec where

import Test.Tasty.Extras

import Plugin.Data.Spec
import Plugin.Lib

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin
import PlutusTx.Test

import Data.Proxy

functions :: TestNested
functions = testNestedGhc "Functions" [
    recursiveFunctions
    , unfoldings
  ]

recursiveFunctions :: TestNested
recursiveFunctions = testNested "recursive" [
    goldenPir "fib" fib
    , goldenUEval "fib4" [ toUPlc fib, toUPlc $ plc (Proxy @"4") (4::Integer) ]
    , goldenPir "sum" sumDirect
    , goldenUEval "sumList" [ toUPlc sumDirect, toUPlc listConstruct3 ]
    , goldenPir "even" evenMutual
    , goldenUEval "even3" [ toUPlc evenMutual, toUPlc $ plc (Proxy @"3") (3::Integer) ]
    , goldenUEval "even4" [ toUPlc evenMutual, toUPlc $ plc (Proxy @"4") (4::Integer) ]
    , goldenPir "strictLength" strictLength
    , goldenPir "lazyLength" lazyLength
  ]

fib :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fib = plc (Proxy @"fib") (
    let fib :: Integer -> Integer
        fib n = if Builtins.equalsInteger n 0
            then 0
            else if Builtins.equalsInteger n 1
            then 1
            else Builtins.addInteger (fib(Builtins.subtractInteger n 1)) (fib(Builtins.subtractInteger n 2))
    in fib)

sumDirect :: CompiledCode ([Integer] -> Integer)
sumDirect = plc (Proxy @"sumDirect") (
    let sum :: [Integer] -> Integer
        sum []     = 0
        sum (x:xs) = Builtins.addInteger x (sum xs)
    in sum)

evenMutual :: CompiledCode (Integer -> Bool)
evenMutual = plc (Proxy @"evenMutual") (
    let even :: Integer -> Bool
        even n = if Builtins.equalsInteger n 0 then True else odd (Builtins.subtractInteger n 1)
        odd :: Integer -> Bool
        odd n = if Builtins.equalsInteger n 0 then False else even (Builtins.subtractInteger n 1)
    in even)

lengthStrict :: [a] -> Integer
lengthStrict l = go 0 l
  where
    go !acc []      = acc
    go !acc (_: tl) = go (acc `Builtins.addInteger` 1) tl

lengthLazy :: [a] -> Integer
lengthLazy l = go 0 l
  where
    go acc []      = acc
    go acc (_: tl) = go (acc `Builtins.addInteger` 1) tl

strictLength :: CompiledCode ([Integer] -> Integer)
strictLength = plc (Proxy @"strictLength") (lengthStrict @Integer)

lazyLength :: CompiledCode ([Integer] -> Integer)
lazyLength = plc (Proxy @"lazyLength") (lengthLazy @Integer)

unfoldings :: TestNested
unfoldings = testNested "unfoldings" [
    goldenPir "nandDirect" nandPlcDirect
    , goldenPir "andDirect" andPlcDirect
    , goldenPir "andExternal" andPlcExternal
    , goldenPir "allDirect" allPlcDirect
    , goldenPir "mutualRecursionUnfoldings" mutualRecursionUnfoldings
    , goldenPir "recordSelector" recordSelector
    , goldenPir "recordSelectorExternal" recordSelectorExternal
    -- We used to have problems with polymorphic let bindings where the generalization was
    -- on the outside of the let, which hit the value restriction. Now we hit the simplifier
    -- it seems to sometimes float these in, but we should keep an eye on these.
    , goldenPir "polyMap" polyMap
    , goldenPir "applicationFunction" applicationFunction
    , goldenPir "unboxedTuples2" unboxedTuples2
    , goldenPir "unboxedTuples3" unboxedTuples3
    , goldenPir "unboxedTuples4" unboxedTuples4
    , goldenPir "unboxedTuples5" unboxedTuples5
    , goldenPir "unboxedTuples2Tuples" unboxedTuples2Tuples
    , goldenPir "unboxedTuples3Tuples" unboxedTuples3Tuples
  ]

andDirect :: Bool -> Bool -> Bool
andDirect = \(a :: Bool) -> \(b::Bool) -> nandDirect (nandDirect a b) (nandDirect a b)

nandDirect :: Bool -> Bool -> Bool
nandDirect = \(a :: Bool) -> \(b::Bool) -> if a then False else if b then False else True

nandPlcDirect :: CompiledCode Bool
nandPlcDirect = plc (Proxy @"nandPlcDirect") (nandDirect True False)

andPlcDirect :: CompiledCode Bool
andPlcDirect = plc (Proxy @"andPlcDirect") (andDirect True False)

andPlcExternal :: CompiledCode Bool
andPlcExternal = plc (Proxy @"andPlcExternal") (andExternal True False)

-- self-recursion
allDirect :: (a -> Bool) -> [a] -> Bool
allDirect p l = case l of
    []  -> True
    h:t -> andDirect (p h) (allDirect p t)

allPlcDirect :: CompiledCode Bool
allPlcDirect = plc (Proxy @"andPlcDirect") (allDirect (\(x::Integer) -> Builtins.lessThanInteger x 5) [7, 6])

mutualRecursionUnfoldings :: CompiledCode Bool
mutualRecursionUnfoldings = plc (Proxy @"mutualRecursionUnfoldings") (evenDirect 4)

recordSelector :: CompiledCode (MyMonoRecord -> Integer)
recordSelector = plc (Proxy @"recordSelector") (\(x :: MyMonoRecord) -> mrA x)

recordSelectorExternal :: CompiledCode (MyExternalRecord -> Integer)
recordSelectorExternal = plc (Proxy @"recordSelectorExternal") (\(x :: MyExternalRecord) -> myExternal x)

mapDirect :: (a -> b) -> [a] -> [b]
mapDirect f l = case l of
    []   -> []
    x:xs -> f x : mapDirect f xs

polyMap :: CompiledCode ([Integer])
polyMap = plc (Proxy @"polyMap") (mapDirect (Builtins.addInteger 1) [0, 1])

myDollar :: (a -> b) -> a -> b
myDollar f a = f a

applicationFunction :: CompiledCode (Integer)
applicationFunction = plc (Proxy @"applicationFunction") ((\x -> Builtins.addInteger 1 x) `myDollar` 1)

unboxedTuple2 :: (# Integer, Integer #) -> Integer
unboxedTuple2 (# i, j #) = i `Builtins.addInteger` j

unboxedTuple3 :: (# Integer, Integer, Integer #) -> Integer
unboxedTuple3 (# i, j, k #) = i `Builtins.addInteger` j `Builtins.addInteger` k

unboxedTuple4 :: (# Integer, Integer, Integer, Integer #) -> Integer
unboxedTuple4 (# i, j, k, l #) = i `Builtins.addInteger` j `Builtins.addInteger` k `Builtins.addInteger` l

unboxedTuple5 :: (# Integer, Integer, Integer, Integer, Integer #) -> Integer
unboxedTuple5 (# i, j, k, l, m #) = i `Builtins.addInteger` j `Builtins.addInteger` k `Builtins.addInteger` l `Builtins.addInteger` m

unboxedTuples2 :: CompiledCode (Integer -> Integer)
unboxedTuples2 = plc (Proxy @"unboxedTuples2") (\x -> let a = unboxedTuple2 (# x, x #) in a)

unboxedTuples3 :: CompiledCode (Integer -> Integer)
unboxedTuples3 = plc (Proxy @"unboxedTuples3") (\x -> let a = unboxedTuple3 (# x, x, x #) in a)

unboxedTuples4 :: CompiledCode (Integer -> Integer)
unboxedTuples4 = plc (Proxy @"unboxedTuples4") (\x -> let a = unboxedTuple4 (# x, x, x, x #) in a)

unboxedTuples5 :: CompiledCode (Integer -> Integer)
unboxedTuples5 = plc (Proxy @"unboxedTuples5") (\x -> let a = unboxedTuple5 (# x, x, x, x, x #) in a)

unboxedTuples2Tuple :: (# (# Integer, Integer, Integer, Integer, Integer #), (# Integer, Integer, Integer, Integer, Integer #) #) -> Integer
unboxedTuples2Tuple (# i, j #) = unboxedTuple5 i `Builtins.addInteger` unboxedTuple5 j

unboxedTuples2Tuples :: CompiledCode (Integer -> Integer)
unboxedTuples2Tuples = plc (Proxy @"unboxedTuples2Tuples") (\x -> let a = unboxedTuples2Tuple (# (# x, x, x, x, x #), (# x, x, x, x, x #) #) in a)

unboxedTuples3Tuple :: (# (# Integer, Integer, Integer, Integer, Integer #), (# Integer, Integer, Integer, Integer, Integer #), (# Integer, Integer, Integer, Integer, Integer #) #) -> Integer
unboxedTuples3Tuple (# i, j, k #) = unboxedTuple5 i `Builtins.addInteger` unboxedTuple5 j `Builtins.addInteger` unboxedTuple5 k

unboxedTuples3Tuples :: CompiledCode (Integer -> Integer)
unboxedTuples3Tuples = plc (Proxy @"unboxedTuples3Tuples") (\x -> let a = unboxedTuples3Tuple (# (# x, x, x, x, x #), (# x, x, x, x, x #), (# x, x, x, x, x #) #) in a)
