{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Basic.Spec where

import Common
import Lib
import PlcTestUtils

import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Plugin

import Data.Proxy


basic :: TestNested
basic = testNested "Basic" [
    goldenPir "monoId" monoId
  , goldenPir "monoK" monoK
  , goldenPir "letFun" letFun
  , goldenPir "nonstrictLet" nonstrictLet
  , goldenPir "strictLet" strictLet
  , goldenPir "strictMultiLet" strictMultiLet
  , goldenPir "strictLetRec" strictLetRec
  -- must keep the scrutinee as it evaluates to error
  , goldenPir "ifOpt" ifOpt
  -- should fail
  , goldenUEval "ifOptEval" [ifOpt]
  ]

monoId :: CompiledCode (Integer -> Integer)
monoId = plc (Proxy @"monoId") (\(x :: Integer) -> x)

monoK :: CompiledCode (Integer -> Integer -> Integer)
monoK = plc (Proxy @"monoK") (\(i :: Integer) -> \(_ :: Integer) -> i)

-- GHC actually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun = plc (Proxy @"letFun") (\(x::Integer) (y::Integer) -> let f z = Builtins.equalsInteger x z in f y)

nonstrictLet :: CompiledCode (Integer -> Integer -> Integer)
nonstrictLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let z = Builtins.addInteger x y in Builtins.addInteger z z)

-- GHC turns strict let-bindings into case expressions, which we correctly turn into strict let-bindings
strictLet :: CompiledCode (Integer -> Integer -> Integer)
strictLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x y in Builtins.addInteger z z)

strictMultiLet :: CompiledCode (Integer -> Integer -> Integer)
strictMultiLet = plc (Proxy @"strictLet") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x y; !q = Builtins.addInteger z z; in Builtins.addInteger q q)

-- Here we see the wrinkles of GHC's codegen: GHC creates let-bindings for the recursion, with _nested_ case expressions for the strictness.
-- So we get non-strict external bindings for z and q, and inside that we get strict bindings corresponding to the case expressions.
strictLetRec :: CompiledCode (Integer -> Integer -> Integer)
strictLetRec = plc (Proxy @"strictLetRec") (\(x::Integer) (y::Integer) -> let !z = Builtins.addInteger x q; !q = Builtins.addInteger y z in Builtins.addInteger z z)

ifOpt :: CompiledCode Integer
ifOpt = plc (Proxy @"ifOpt") (if ((1 `Builtins.divideInteger` 0) `Builtins.equalsInteger` 0) then 1 else 1)
