{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin PlutusTx.Plugin #-}
{-# OPTIONS -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Basic.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Lib

import qualified PlutusTx.Builtins   as Builtins
import           PlutusTx.Code
import           PlutusTx.Plugin

import qualified PlutusCore.Builtins as PLC
import qualified PlutusCore.Universe as PLC

import           Data.Proxy

basic :: TestNested
basic = testNested "Basic" [
    goldenPir "monoId" monoId
  , goldenPir "monoK" monoK
  , goldenPir "letFun" letFun
  -- must keep the scrutinee as it evaluates to error
  , goldenPir "ifOpt" ifOpt
  -- should fail
  , goldenUEval "ifOptEval" [ifOpt]
  ]

monoId :: CompiledCode (Integer -> Integer)
monoId = plc (Proxy @"monoId") (\(x :: Integer) -> x)

monoK :: CompiledCode (Integer -> Integer -> Integer)
monoK = plc (Proxy @"monoK") (\(i :: Integer) -> \(j :: Integer) -> i)

-- GHC acutually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun = plc (Proxy @"letFun") (\(x::Integer) (y::Integer) -> let f z = Builtins.equalsInteger x z in f y)

ifOpt :: CompiledCode Integer
ifOpt = plc (Proxy @"ifOpt") (if ((1 `Builtins.divideInteger` 0) `Builtins.equalsInteger` 0) then 1 else 1)
