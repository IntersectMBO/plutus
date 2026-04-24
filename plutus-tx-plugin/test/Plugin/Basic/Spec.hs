{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant if" #-}

module Plugin.Basic.Spec where

import Plinth.Plugin (plinthc)
import PlutusCore.Test (goldenUEval)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.HasOpaque qualified as P
import PlutusTx.Code (CompiledCode)
import PlutusTx.Prelude qualified as P
import PlutusTx.Test (goldenPirReadable, goldenUPlc)

import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

basic :: TestNested
basic =
  testNested "Basic" . pure $
    testNestedGhc
      [ goldenPirReadable "monoId" monoId
      , goldenPirReadable "monoK" monoK
      , goldenPirReadable "letFun" letFun
      , goldenPirReadable "nonstrictLet" nonstrictLet
      , goldenPirReadable "strictLet" strictLet
      , goldenPirReadable "strictMultiLet" strictMultiLet
      , goldenPirReadable "strictLetRec" strictLetRec
      , -- must keep the scrutinee as it evaluates to error
        goldenPirReadable "ifOpt" ifOpt
      , -- should fail
        goldenUEval "ifOptEval" [ifOpt]
      , goldenPirReadable "monadicDo" monadicDo
      , goldenPirReadable "patternMatchDo" patternMatchDo
      , goldenUPlc "patternMatchFailure" patternMatchFailure
      , goldenPirReadable "defaultCaseDuplication" defaultCaseDuplication
      , goldenPirReadable "defaultCaseDuplicationNested" defaultCaseDuplicationNested
      , goldenPirReadable "integerPatternMatch" integerPatternMatch
      , goldenPirReadable "integerCase" integerCase
      , goldenPirReadable "emptyBoolArray" emptyBoolArray
      , goldenPirReadable "emptyByteStringArray" emptyByteStringArray
      , goldenPirReadable "emptyComplexArray" emptyComplexArray
      ]

emptyBoolArray :: CompiledCode (P.BuiltinList (P.BuiltinList Bool))
emptyBoolArray = plinthc (P.mkNil @(P.BuiltinList Bool))

emptyByteStringArray :: CompiledCode (P.BuiltinList P.BuiltinByteString)
emptyByteStringArray = plinthc (P.mkNil @P.BuiltinByteString)

emptyComplexArray
  :: CompiledCode
       ( P.BuiltinList
           ( P.BuiltinList
               (P.BuiltinPair P.BuiltinByteString (P.BuiltinPair (P.BuiltinList Integer) Bool))
           )
       )
emptyComplexArray = plinthc P.mkNil

monoId :: CompiledCode (Integer -> Integer)
monoId = plinthc \(x :: Integer) -> x

monoK :: CompiledCode (Integer -> Integer -> Integer)
monoK = plinthc \(i :: Integer) (_ :: Integer) -> i

-- GHC actually turns this into a lambda for us, try and make one that stays a let
letFun :: CompiledCode (Integer -> Integer -> Bool)
letFun = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let f z = Builtins.equalsInteger x z in f y

nonstrictLet :: CompiledCode (Integer -> Integer -> Integer)
nonstrictLet = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let z = Builtins.addInteger x y
     in Builtins.addInteger z z

-- GHC turns strict let-bindings into case expressions,
-- which we correctly turn into strict let-bindings
strictLet :: CompiledCode (Integer -> Integer -> Integer)
strictLet = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let !z = Builtins.addInteger x y
     in Builtins.addInteger z z

strictMultiLet :: CompiledCode (Integer -> Integer -> Integer)
strictMultiLet = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let !z = Builtins.addInteger x y
        !q = Builtins.addInteger z z
     in Builtins.addInteger q q

-- Here we see the wrinkles of GHC's codegen: GHC creates let-bindings for the recursion,
-- with _nested_ case expressions for the strictness.
-- So we get non-strict external bindings for z and q, and inside that we get strict bindings
-- corresponding to the case expressions.
strictLetRec :: CompiledCode (Integer -> Integer -> Integer)
strictLetRec = plinthc do
  \(x :: Integer) (y :: Integer) ->
    let !z = Builtins.addInteger x q
        !q = Builtins.addInteger y z
     in Builtins.addInteger z z

ifOpt :: CompiledCode Integer
ifOpt = plinthc do
  if (1 `Builtins.divideInteger` 0) `Builtins.equalsInteger` 0 then 1 else 1

-- TODO: It's pretty questionable that this works at all! It's actually using 'Monad' from 'base',
-- since that's what 'do' notation is hard-coded to use, and it just happens that it's all inlinable
-- enough to work...
-- Test what basic do-notation looks like (should just be a bunch of calls to '>>=')
monadicDo :: CompiledCode (Maybe Integer -> Maybe Integer -> Maybe Integer)
monadicDo = plinthc do
  \(x :: Maybe Integer) (y :: Maybe Integer) -> do
    x' <- x
    y' <- y
    P.pure (x' `Builtins.addInteger` y')

-- Irrefutable match in a do block
patternMatchDo :: CompiledCode (Maybe (Integer, Integer) -> Maybe Integer -> Maybe Integer)
patternMatchDo = plinthc do
  \(x :: Maybe (Integer, Integer)) (y :: Maybe Integer) -> do
    (x1, x2) <- x
    y' <- y
    P.pure (x1 `Builtins.addInteger` x2 `Builtins.addInteger` y')

-- Should fail, since it'll call 'MonadFail.fail' with a String, which won't work
patternMatchFailure :: CompiledCode (Maybe (Maybe Integer) -> Maybe Integer -> Maybe Integer)
patternMatchFailure = plinthc do
  \(x :: Maybe (Maybe Integer)) (y :: Maybe Integer) -> do
    Just x' <- x
    y' <- y
    P.pure (x' `Builtins.addInteger` y')

data A = B | C | D

-- We don't want to duplicate the RHS of the default case
defaultCaseDuplication :: CompiledCode (A -> Integer)
defaultCaseDuplication = plinthc do
  \(x :: A) ->
    case x of
      B -> 1
      _ -> 2

-- If we do duplicate the RHS of default cases, then here we will end up with
-- 4 copies of the literal 3, showing how this can become exponential
defaultCaseDuplicationNested :: CompiledCode (A -> A -> Integer)
defaultCaseDuplicationNested = plinthc do
  \(x :: A) (y :: A) ->
    case x of
      B -> 1
      _ ->
        case y of
          B -> 2
          _ -> 3

integerCase :: CompiledCode Integer
integerCase = plinthc ((\case 1 -> 42; 2 -> 100; _ -> -1) (2 :: Integer))

integerMatchFunction :: Integer -> Integer
integerMatchFunction 1 = 12
integerMatchFunction 2 = 22
integerMatchFunction _ = 42
-- We need NOINLINE, because otherwise the plugin automatically inserts INLINEABLE.
-- With INLINEABLE, GHC generates `case` on Integer in Core, causing the plugin to
-- error with "Cannot case on a value on type: GHC.Num.Integer.Integer".
{-# NOINLINE integerMatchFunction #-}

integerPatternMatch :: CompiledCode Integer
integerPatternMatch = plinthc (integerMatchFunction 2)

{- Note [NOINLINE in some tests]

We need NOINLINE in some test cases that match on integers (which one isn't supposed to do
in Plinth), because otherwise the plugin automatically inserts INLINEABLE. With INLINEABLE,
GHC generates `case` on Integer in Core, causing the plugin to error with
"Cannot case on a value on type: GHC.Num.Integer.Integer".
-}
