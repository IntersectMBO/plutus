{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE Strict            #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -ddump-simpl-iterations -dsuppress-all #-}
{-# OPTIONS_GHC -fno-float-in #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-local-float-out #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module BuiltinUnit.Spec where

import PlutusTx.Prelude
import Prelude (IO, seq)

import Control.Lens (view)
import PlutusTx (CompiledCode, compile, getPlcNoAnn)
import PlutusTx.Builtins.Internal (unitval)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase)
import UntypedPlutusCore (progTerm)

tests :: TestTree
tests =
  testGroup
    "BuiltinUnit"
    [ testCase "error ()" do assertCompiledTerm code1
    , testCase "unitval" do assertCompiledTerm code2
    , testCase "locally defined constructor" do assertCompiledTerm code3
    , testCase "toOpaque ()" do assertCompiledTerm code4
    ]

{- GHC Core after simplification:

code1 = case error () of
  validator1_X0 { BuiltinUnit ipv_smFH -> plc Proxy validator1_X0 }

code2 = case unitval of
  validator2_X0 { BuiltinUnit ipv_smFJ -> plc Proxy validator2_X0 }

code3 = case unitval of
  builtinUnit_X0 { BuiltinUnit ipv_smFL -> plc Proxy builtinUnit_X0 }

code4 = case toOpaque $fHasToOpaque()BuiltinUnit () of
  validator4_X0 { BuiltinUnit ipv_smGp -> plc Proxy validator4_X0 }

Compilation error:

<no location info>: error:
    GHC Core to PLC plugin:
    Error: Unsupported feature:
    Cannot construct a value of type: BuiltinUnit
    Note: GHC can generate these unexpectedly, you may need
    '-fno-strictness', '-fno-specialise', '-fno-spec-constr',
    '-fno-unbox-strict-fields', or '-fno-unbox-small-strict-fields'.
Context: Compiling expr: BuiltinUnit
Context: Compiling expr: BuiltinUnit ipv
Context: Compiling definition of: validator1
Context: Compiling expr: validator1
Context: Compiling expr at: test/BuiltinUnit/Spec.hs:75:11-36
Context: Compiling expr: validator1
-}

code1 :: CompiledCode BuiltinUnit
code1 = $$(compile [||validator1||])
 where
  validator1 :: BuiltinUnit
  validator1 = PlutusTx.Prelude.error ()
  {-# INLINEABLE validator1 #-}

code2 :: CompiledCode BuiltinUnit
code2 = $$(compile [||validator2||])
 where
  validator2 :: BuiltinUnit
  validator2 = unitval
  {-# INLINEABLE validator2 #-}

code3 :: CompiledCode BuiltinUnit
code3 = $$(compile [||validator3||])
 where
  validator3 :: BuiltinUnit
  validator3 = builtinUnit
  {-# INLINEABLE validator3 #-}

  builtinUnit :: BuiltinUnit
  builtinUnit = unitval
  {-# INLINEABLE builtinUnit #-}

code4 :: CompiledCode BuiltinUnit
code4 = $$(compile [||validator4||])
 where
  validator4 :: BuiltinUnit
  validator4 = toOpaque ()
  {-# INLINEABLE validator4 #-}

assertCompiledTerm :: CompiledCode a -> Assertion
assertCompiledTerm code = view progTerm (getPlcNoAnn code) `seq` return @IO ()
