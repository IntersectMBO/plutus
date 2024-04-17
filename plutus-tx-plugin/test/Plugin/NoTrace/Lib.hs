{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Plugin.NoTrace.Lib where

import Prelude hiding (Show, show, (+))

import Control.Lens (universeOf, (&), (^.))
import GHC.Exts (noinline)
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParameters)
import PlutusTx.Builtins (BuiltinString, appendString, error)
import PlutusTx.Code (CompiledCode, getPlc, getPlcNoAnn)
import PlutusTx.Numeric ((+))
import PlutusTx.Show.TH (Show (show))
import PlutusTx.Trace (trace, traceError)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek (counting, noEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (runCekDeBruijn)

data Arg = MkArg

instance Show Arg where
  show MkArg = "MkArg"

countTraces :: CompiledCode a -> Int
countTraces code =
  length
    [ subterm
    | let term = getPlcNoAnn code ^. UPLC.progTerm
    , subterm@(UPLC.Builtin _ Builtin.Trace) <- universeOf UPLC.termSubterms term
    ]

evaluatesToError :: CompiledCode a -> Bool
evaluatesToError = not . evaluatesWithoutError

evaluatesWithoutError :: CompiledCode a -> Bool
evaluatesWithoutError code =
  runCekDeBruijn defaultCekParameters counting noEmitter (getPlc code ^. UPLC.progTerm) & \case
    (Left _exception, _counter, _logs) -> False
    (Right _result, _counter, _logs) -> True

----------------------------------------------------------------------------------------------------
-- Functions that contain traces -------------------------------------------------------------------

traceArgument :: BuiltinString -> ()
traceArgument x = trace x ()

traceShow :: ()
traceShow =
  let f :: (Show s) => s -> ()
      f s = trace (show s) ()
   in noinline f MkArg

traceDirect :: ()
traceDirect = trace "test" ()

traceNonConstant :: (BuiltinString -> BuiltinString)
traceNonConstant x = trace "!!!" (x `appendString` "7")

traceComplex :: (Bool -> ())
traceComplex b =
  if b
    then trace "yes" ()
    else traceError "no" ()

traceRepeatedly :: Integer
traceRepeatedly =
  let i1 = trace "Making my first int" (1 :: Integer)
      i2 = trace "Making my second int" (2 :: Integer)
      i3 = trace "Adding them up" (i1 + i2)
   in i3

traceImpure :: ()
traceImpure = trace ("Message: " `appendString` PlutusTx.Builtins.error ()) ()
