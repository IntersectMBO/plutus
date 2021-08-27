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
  goldenUEvalProfile "fib4" [ toUPlc fibTest, toUPlc $ plc (Proxy @"4") (4::Integer) ]
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

