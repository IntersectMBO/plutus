-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

-- | Tests for the profiling machinery.

module Plugin.Profiling.Spec where

import Test.Tasty.Extras

import PlutusCore.Test (ToUPlc (toUPlc), goldenUEvalProfile)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode)
import PlutusTx.Plugin (plc)
import PlutusTx.Test (goldenPir)

import Data.Functor.Identity
import Data.Proxy (Proxy (Proxy))
import Prelude

profiling :: TestNested
profiling = testNestedGhc "Profiling" [
  goldenPir "fib" fibTest
  , goldenUEvalProfile "fib4" [toUPlc fibTest, toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "fact4" [toUPlc factTest, toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenPir "addInt" addIntTest
  , goldenUEvalProfile "addInt3" [toUPlc addIntTest, toUPlc $ plc (Proxy @"3") (3::Integer)]
  , goldenUEvalProfile "letInFun" [toUPlc letInFunTest, toUPlc $ plc (Proxy @"1") (1::Integer), toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "letInFunMoreArg" [toUPlc letInFunMoreArgTest, toUPlc $ plc (Proxy @"1") (1::Integer), toUPlc $ plc (Proxy @"4") (4::Integer), toUPlc $ plc (Proxy @"5") (5::Integer)]
  , goldenUEvalProfile "letRecInFun" [toUPlc letRecInFunTest, toUPlc $ plc (Proxy @"3") (3::Integer)]
  , goldenPir "idCode" idTest
  , goldenUEvalProfile "id" [toUPlc idTest]
  , goldenUEvalProfile "swap" [toUPlc swapTest]
  , goldenUEvalProfile "typeclass" [toUPlc typeclassTest, toUPlc $ plc (Proxy @"1") (1::Integer), toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "argMismatch1" [toUPlc argMismatch1]
  , goldenUEvalProfile "argMismatch2" [toUPlc argMismatch2]
  ]

fact :: Integer -> Integer
fact n =
  if Builtins.equalsInteger n 0
    then 1
    else Builtins.multiplyInteger n (fact (Builtins.subtractInteger n 1))

factTest :: CompiledCode (Integer -> Integer)
factTest = plc (Proxy @"fact") fact

fib :: Integer -> Integer
fib n = if Builtins.equalsInteger n 0
          then 0
          else if Builtins.equalsInteger n 1
          then 1
          else Builtins.addInteger (fib(Builtins.subtractInteger n 1)) (fib(Builtins.subtractInteger n 2))

fibTest :: CompiledCode (Integer -> Integer)
-- not using case to avoid literal cases
fibTest = plc (Proxy @"fib") fib

addInt :: Integer -> Integer -> Integer
addInt x = Builtins.addInteger x

addIntTest :: CompiledCode (Integer -> Integer -> Integer)
addIntTest = plc (Proxy @"addInt") addInt

-- \x y -> let f z = z + 1 in f x + f y
letInFunTest :: CompiledCode (Integer -> Integer -> Integer)
letInFunTest =
  plc
    (Proxy @"letInFun")
    (\(x::Integer) (y::Integer)
      -> let f z = Builtins.addInteger z 1 in Builtins.addInteger (f x) (f y))

-- \x y z -> let f n = n + 1 in z * (f x + f y)
letInFunMoreArgTest :: CompiledCode (Integer -> Integer -> Integer -> Integer)
letInFunMoreArgTest =
  plc
    (Proxy @"letInFun")
    (\(x::Integer) (y::Integer) (z::Integer)
      -> let f n = Builtins.addInteger n 1 in
        Builtins.multiplyInteger z (Builtins.addInteger (f x) (f y)))

-- Try a recursive function so it definitely won't be inlined
letRecInFunTest :: CompiledCode (Integer -> Integer)
letRecInFunTest =
  plc
    (Proxy @"letRecInFun")
    (\(x::Integer) -> let f n = if Builtins.equalsInteger n 0 then 0 else Builtins.addInteger 1 (f (Builtins.subtractInteger n 1)) in f x)

idTest :: CompiledCode Integer
idTest = plc (Proxy @"id") (id (id (1::Integer)))

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

swapTest :: CompiledCode (Integer, Bool)
swapTest = plc (Proxy @"swap") (swap (True,1))

-- Two method typeclasses definitely get dictionaries, rather than just being passed as single functions
class TwoMethods a where
    methodA :: a -> a -> Integer
    methodB :: a -> a -> Integer

instance TwoMethods Integer where
    {-# INLINABLE methodA #-}
    methodA = Builtins.addInteger
    {-# INLINABLE methodB #-}
    methodB = Builtins.subtractInteger

-- Make a function that uses the typeclass polymorphically to check that
useTypeclass :: TwoMethods a => a -> a -> Integer
useTypeclass a b = Builtins.addInteger (methodA a b) (methodB a b)

-- Check that typeclass methods get traces
typeclassTest :: CompiledCode (Integer -> Integer -> Integer)
typeclassTest = plc (Proxy @"typeclass") (\(x::Integer) (y::Integer) -> useTypeclass x y)

{-# INLINABLE newtypeFunction #-}
newtypeFunction :: a -> Identity (a -> a)
newtypeFunction _ = Identity (\a -> a)

argMismatch1 :: CompiledCode Integer
argMismatch1 = plc (Proxy @"argMismatch1") (runIdentity (newtypeFunction 1) 1)

{-# INLINABLE obscuredFunction #-}
obscuredFunction :: (a -> a -> a) -> a -> a -> a
obscuredFunction f a = f a

argMismatch2 :: CompiledCode Integer
argMismatch2 = plc (Proxy @"argMismatch2") (obscuredFunction (\a _ -> a) 1 2)
