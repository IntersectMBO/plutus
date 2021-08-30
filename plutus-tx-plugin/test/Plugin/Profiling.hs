{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

module Plugin.Profiling where
import           Common
import           Lib                     (goldenPir)
import           PlcTestUtils            (ToUPlc (toUPlc), goldenUEvalProfile)
import           Plugin.Basic.Spec
import           Plugin.Lib              (MyExternalRecord (myExternal), andExternal, evenDirect)

import           Plugin.Data.Spec
import           Plugin.Functions.Spec   hiding (fib, recursiveFunctions)
import           Plugin.Typeclasses.Spec
import qualified PlutusTx.Builtins       as Builtins
import           PlutusTx.Code           (CompiledCode)
import           PlutusTx.Plugin         (plc)

import qualified PlutusCore.Default      as PLC

import           Data.Proxy
import           Data.Text               (Text)

profiling :: TestNested
profiling = testNested "Profiling" [
  goldenUEvalProfile "fib" [toUPlc fibTest]
  , goldenUEvalProfile "fib4" [toUPlc fibTest, toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "addInt" [toUPlc addIntTest]
  , goldenUEvalProfile "id" [toUPlc idTest, toUPlc $ plc (Proxy @"1") (1::Integer)]
  , goldenUEvalProfile "swap" [toUPlc swapTest]
  ]

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

idForAll :: a -> a
idForAll a = a

idTest :: CompiledCode (a -> a)
idTest = plc (Proxy @"id") idForAll

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

swapTest :: CompiledCode ((a,b) -> (b,a))
swapTest = plc (Proxy @"swap") swap
