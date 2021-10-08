{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

-- | Tests for the profiling machinery.

module Plugin.Profiling.Spec where
import           Common
import           Lib                       (goldenPir)
import           PlcTestUtils              (ToUPlc (toUPlc), goldenUEvalProfile, rethrow, runUPlcProfile)
import           Plugin.Basic.Spec
import           Plugin.Lib                (MyExternalRecord (myExternal), andExternal, evenDirect)

import           Plugin.Data.Spec
import           Plugin.Functions.Spec     hiding (fib, recursiveFunctions)
import           Plugin.Typeclasses.Spec
import qualified PlutusCore.Default        as PLC
import qualified PlutusTx.Builtins         as Builtins
import           PlutusTx.Code             (CompiledCode)
import           PlutusTx.Plugin           (plc)

import           Control.Lens.Combinators  (_2)
import           Control.Lens.Getter       (view)
import           Data.Proxy                (Proxy (Proxy))
import           Data.Text                 (Text)
import qualified PlutusCore.Default        as Builtins
import           Prelude
import           Prettyprinter.Internal    (pretty)
import           Prettyprinter.Render.Text (hPutDoc)
import           System.IO                 (IOMode (WriteMode), withFile)

profiling :: TestNested
profiling = testNested "Profiling" [
  goldenUEvalProfile "fib" [toUPlc fibTest]
  , goldenUEvalProfile "fib4" [toUPlc fibTest, toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "fact4" [toUPlc factTest, toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "addInt" [toUPlc addIntTest]
  , goldenUEvalProfile "addInt3" [toUPlc addIntTest, toUPlc  $ plc (Proxy @"3") (3::Integer)]
  , goldenUEvalProfile "letInFun" [toUPlc letInFunTest, toUPlc $ plc (Proxy @"1") (1::Integer), toUPlc $ plc (Proxy @"4") (4::Integer)]
  , goldenUEvalProfile "letInFunMoreArg" [toUPlc letInFunMoreArgTest, toUPlc $ plc (Proxy @"1") (1::Integer), toUPlc $ plc (Proxy @"4") (4::Integer), toUPlc $ plc (Proxy @"5") (5::Integer)]
  -- ghc does the function application
  , goldenUEvalProfile "id" [toUPlc idTest]
  , goldenUEvalProfile "swap" [toUPlc swapTest]
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

idTest :: CompiledCode Integer
idTest = plc (Proxy @"id") (id (1::Integer))

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

swapTest :: CompiledCode (Integer, Bool)
swapTest = plc (Proxy @"swap") (swap (True,1))
