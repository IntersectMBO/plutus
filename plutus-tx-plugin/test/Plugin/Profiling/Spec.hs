{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:profile-all #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use guards" #-}
{-# HLINT ignore "Redundant id" #-}
{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Use const" #-}

-- | Tests for the profiling machinery.
module Plugin.Profiling.Spec where

import Test.Tasty.Extras

import Plinth.Plugin (plinthc)
import PlutusCore.Test (ToUPlc (toUPlc), goldenUEvalLogs)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode)
import PlutusTx.Test (goldenPirReadable)

import Data.Functor.Identity
import Prelude

profiling :: TestNested
profiling =
  testNested "Profiling" . pure $ do
    testNestedGhc
      [ goldenPirReadable "fib" fibTest
      , goldenUEvalLogs
          "fib4"
          [ toUPlc fibTest
          , toUPlc $ plinthc (4 :: Integer)
          ]
      , goldenUEvalLogs
          "fact4"
          [ toUPlc factTest
          , toUPlc $ plinthc (4 :: Integer)
          ]
      , goldenPirReadable "addInt" addIntTest
      , goldenUEvalLogs
          "addInt3"
          [ toUPlc addIntTest
          , toUPlc $ plinthc (3 :: Integer)
          ]
      , goldenUEvalLogs
          "letInFun"
          [ toUPlc letInFunTest
          , toUPlc $ plinthc (1 :: Integer)
          , toUPlc $ plinthc (4 :: Integer)
          ]
      , goldenUEvalLogs
          "letInFunMoreArg"
          [ toUPlc letInFunMoreArgTest
          , toUPlc $ plinthc (1 :: Integer)
          , toUPlc $ plinthc (4 :: Integer)
          , toUPlc $ plinthc (5 :: Integer)
          ]
      , goldenUEvalLogs
          "letRecInFun"
          [ toUPlc letRecInFunTest
          , toUPlc $ plinthc (3 :: Integer)
          ]
      , goldenPirReadable "idCode" idTest
      , goldenUEvalLogs "id" [toUPlc idTest]
      , goldenUEvalLogs "swap" [toUPlc swapTest]
      , goldenUEvalLogs
          "typeclass"
          [ toUPlc typeclassTest
          , toUPlc $ plinthc (1 :: Integer)
          , toUPlc $ plinthc (4 :: Integer)
          ]
      , goldenUEvalLogs "argMismatch1" [toUPlc argMismatch1]
      , goldenUEvalLogs "argMismatch2" [toUPlc argMismatch2]
      ]

fact :: Integer -> Integer
fact n =
  if Builtins.equalsInteger n 0
    then 1
    else Builtins.multiplyInteger n (fact (Builtins.subtractInteger n 1))

factTest :: CompiledCode (Integer -> Integer)
factTest = plinthc fact

fib :: Integer -> Integer
fib n =
  if Builtins.equalsInteger n 0
    then 0
    else
      if Builtins.equalsInteger n 1
        then 1
        else
          Builtins.addInteger
            (fib (Builtins.subtractInteger n 1))
            (fib (Builtins.subtractInteger n 2))

fibTest :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fibTest = plinthc fib

addInt :: Integer -> Integer -> Integer
addInt x = Builtins.addInteger x

addIntTest :: CompiledCode (Integer -> Integer -> Integer)
addIntTest = plinthc addInt

-- \x y -> let f z = z + 1 in f x + f y
letInFunTest :: CompiledCode (Integer -> Integer -> Integer)
letInFunTest = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let f z = Builtins.addInteger z 1 in Builtins.addInteger (f x) (f y)

-- \x y z -> let f n = n + 1 in z * (f x + f y)
letInFunMoreArgTest :: CompiledCode (Integer -> Integer -> Integer -> Integer)
letInFunMoreArgTest = plinthc do
  \(x :: Integer) (y :: Integer) (z :: Integer) ->
    let f n = Builtins.addInteger n 1
     in Builtins.multiplyInteger z (Builtins.addInteger (f x) (f y))

-- Try a recursive function so it definitely won't be inlined
letRecInFunTest :: CompiledCode (Integer -> Integer)
letRecInFunTest = plinthc do
  \(x :: Integer) ->
    let f n =
          if Builtins.equalsInteger n 0
            then 0
            else Builtins.addInteger 1 (f (Builtins.subtractInteger n 1))
     in f x

idTest :: CompiledCode Integer
idTest = plinthc do
  id (id (1 :: Integer))

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

swapTest :: CompiledCode (Integer, Bool)
swapTest = plinthc (swap (True, 1))

-- Two method typeclasses definitely get dictionaries,
-- rather than just being passed as single functions
class TwoMethods a where
  methodA :: a -> a -> Integer
  methodB :: a -> a -> Integer

instance TwoMethods Integer where
  {-# INLINEABLE methodA #-}
  methodA = Builtins.addInteger
  {-# INLINEABLE methodB #-}
  methodB = Builtins.subtractInteger

-- Make a function that uses the typeclass polymorphically to check that
useTypeclass :: TwoMethods a => a -> a -> Integer
useTypeclass a b = Builtins.addInteger (methodA a b) (methodB a b)

-- Check that typeclass methods get traces
typeclassTest :: CompiledCode (Integer -> Integer -> Integer)
typeclassTest = plinthc do
  \(x :: Integer) (y :: Integer) -> useTypeclass x y

newtypeFunction :: a -> Identity (a -> a)
newtypeFunction _ = Identity (\a -> a)
{-# INLINEABLE newtypeFunction #-}

argMismatch1 :: CompiledCode Integer
argMismatch1 = plinthc do
  runIdentity (newtypeFunction 1) 1

obscuredFunction :: (a -> a -> a) -> a -> a -> a
obscuredFunction f a = f a
{-# INLINEABLE obscuredFunction #-}

argMismatch2 :: CompiledCode Integer
argMismatch2 = plinthc do
  obscuredFunction (\a _ -> a) 1 2
