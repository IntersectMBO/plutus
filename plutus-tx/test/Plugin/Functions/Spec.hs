{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Functions.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import           Plugin.Data.Spec

import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Plugin

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

functions :: TestNested
functions = testNested "Functions" [
    recursiveFunctions
    , unfoldings
  ]

recursiveFunctions :: TestNested
recursiveFunctions = testNested "recursive" [
    goldenPir "fib" fib
    , goldenEval "fib4" [ getProgram fib, getProgram $ plc @"4" (4::Integer) ]
    , goldenPir "sum" sumDirect
    , goldenEval "sumList" [ getProgram sumDirect, getProgram listConstruct3 ]
    , goldenPir "even" evenMutual
    , goldenEval "even3" [ getProgram evenMutual, getProgram $ plc @"3" (3::Integer) ]
    , goldenEval "even4" [ getProgram evenMutual, getProgram $ plc @"4" (4::Integer) ]
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
    -- We used to have problems with polymorphic let bindings where the generalization was
    -- on the outside of the let, which hit the value restriction. Now we hit the simplifier
    -- it seems to sometimes float these in, but we should keep an eye on these.
    , goldenPir "polyMap" polyMap
    , goldenPir "applicationFunction" applicationFunction
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

mapDirect :: (a -> b) -> [a] -> [b]
mapDirect f l = case l of
    []   -> []
    x:xs -> f x : mapDirect f xs

polyMap :: CompiledCode ([Integer])
polyMap = plc @"polyMap" (mapDirect (Builtins.addInteger 1) [0, 1])

myDollar :: (a -> b) -> a -> b
myDollar f a = f a

applicationFunction :: CompiledCode (Integer)
applicationFunction = plc @"applicationFunction" ((\x -> Builtins.addInteger 1 x) `myDollar` 1)
