{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module DropList.Spec where

import PlutusTx
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code
import PlutusTx.Coverage
import PlutusTx.List qualified
import PlutusTx.Prelude
import PlutusTx.Test hiding (Term)
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

import Control.Exception
import Data.Functor
import PlutusCore.Annotation
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Version (plcVersion110)
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

import Prelude qualified as Haskell

tests :: TestNested
tests =
  testNested "DropList"
    . pure
    $ testNestedGhc
      [ goldenUPlcReadable "dropListSOP"
          (dropListSOP `app` (liftCodeDef 100) `app` (liftCode110Norm [1..200]))
      , goldenEvalCekCatchBudget "dropListSOP"
          (dropListSOP `app` (liftCodeDef 100) `app` (liftCode110Norm [1..200]))
      , goldenUPlcReadable "dropListBuiltinRec"
          (dropListBuiltinRec `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      , goldenEvalCekCatchBudget "dropListBuiltinRec"
          (dropListBuiltinRec `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      , goldenUPlcReadable "dropListBuiltinRecUnrolled"
          (dropListBuiltinRecUnrolled `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      , goldenEvalCekCatchBudget "dropListBuiltinRecUnrolled"
          (dropListBuiltinRecUnrolled `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      , goldenUPlcReadable "dropListBuiltin"
          (dropListBuiltin `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      , goldenEvalCekCatchBudget "dropListBuiltin"
          (dropListBuiltin `app` (liftCodeDef 100) `app` (liftCode110Norm bigList))
      ]

unsafeRunCekRes :: Term NamedDeBruijn DefaultUni DefaultFun () -> Term NamedDeBruijn DefaultUni DefaultFun SrcSpans
unsafeRunCekRes x =
  case runCekRes x of
    Right x' -> x $> Haskell.mempty
    Left _   -> error () "no"

runCekRes :: (t ~ Term NamedDeBruijn DefaultUni DefaultFun ())
             => t -> Either (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun) t
runCekRes t =
    UPLC.cekResultToEither . UPLC._cekReportResult $
    UPLC.runCekDeBruijn defaultCekParametersForTesting restrictingEnormous noEmitter t

liftCode110 :: Lift DefaultUni a => a -> CompiledCode a
liftCode110 = liftCode plcVersion110

liftCode110Norm :: Lift DefaultUni a => a -> CompiledCode a
liftCode110Norm x =
  DeserializedCode
    (Program Haskell.mempty plcVersion110 (unsafeRunCekRes $ _progTerm $ getPlcNoAnn $ liftCode110 $ x))
    Nothing
    Haskell.mempty

app :: CompiledCode (a -> b) -> CompiledCode a -> CompiledCode b
app f x =
  case UPLC.applyProgram (getPlc f) (getPlc x) of
    Right res -> DeserializedCode res Nothing Haskell.mempty
    Left _    -> Haskell.error "no"


bigList :: BuiltinList Integer
bigList = toOpaque $ [1..200 :: Integer] -- PlutusTx.List.replicate 200 (42 :: Integer)


dropListSOP :: CompiledCode (Integer -> [Integer] -> [Integer])
dropListSOP = $$(compile [|| dropListSOP' ||])

dropListSOP' :: Integer -> [Integer] -> [Integer]
dropListSOP' 0 li     = li
dropListSOP' n (x:xs) = dropListSOP' (n - 1) xs

dropListBuiltinRec :: CompiledCode (Integer -> BuiltinList Integer -> BuiltinList Integer)
dropListBuiltinRec = $$(compile [|| dropListBuiltinRec' ||])

dropListBuiltinRec' :: Integer -> BuiltinList Integer -> BuiltinList Integer
dropListBuiltinRec' n li =
  if n == 0 then li else dropListBuiltinRec' (n - 1) (BI.tail li)

dropListBuiltinRecUnrolled :: CompiledCode (Integer -> BuiltinList Integer -> BuiltinList Integer)
dropListBuiltinRecUnrolled = $$(compile [|| dropListBuiltinRecUnrolled' ||])

dropListBuiltinRecUnrolled' :: Integer -> BuiltinList Integer -> BuiltinList Integer
dropListBuiltinRecUnrolled' n li =
  if n == 0
  then li
  else if n == 1
  then BI.tail li
  else if n == 2
  then BI.tail $ BI.tail li
  else if n == 3
  then BI.tail $ BI.tail $ BI.tail li
  else if n == 4
  then BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 5
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 6
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 7
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 8
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 9
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else if n == 10
  then BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li
  else dropListBuiltinRecUnrolled' (n - 10) (BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail $ BI.tail li)

dropListBuiltin :: CompiledCode (Integer -> BuiltinList Integer -> BuiltinList Integer)
dropListBuiltin = $$(compile [|| dropListBuiltin' ||])

dropListBuiltin' :: Integer -> BuiltinList Integer -> BuiltinList Integer
dropListBuiltin' n li = BI.drop n li
