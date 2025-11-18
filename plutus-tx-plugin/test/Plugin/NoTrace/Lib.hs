{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Plugin.NoTrace.Lib where

import Prelude hiding (Show, show, (+))

import Control.Lens (universeOf, (^.))
import GHC.Exts (noinline)
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusTx.Builtins (BuiltinString, appendString, error)
import PlutusTx.Code (CompiledCode, getPlcNoAnn)
import PlutusTx.Numeric ((+))
import PlutusTx.Show.TH (Show (show))
import PlutusTx.Trace (trace, traceError)
import UntypedPlutusCore qualified as UPLC

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

----------------------------------------------------------------------------------------------------
-- Functions that contain traces -------------------------------------------------------------------

traceArgument :: BuiltinString -> ()
traceArgument x = trace x ()

traceShow :: ()
traceShow =
  let f :: Show s => s -> ()
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
