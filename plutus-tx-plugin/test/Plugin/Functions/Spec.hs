{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin -fplugin-opt PlutusTx.Plugin:defer-errors -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Functions.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Lib

import           Plugin.Data.Spec

import qualified PlutusTx.Builtins  as Builtins
import           PlutusTx.Code
import           PlutusTx.Plugin

import qualified PlutusCore.Default as PLC

import           Data.Proxy

functions :: TestNested
functions = testNested "Functions" [
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
allPlcDirect = plc (Proxy @"andPlcDirect") (allDirect (\(x::Integer) -> Builtins.greaterThanInteger x 5) [7, 6])

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
