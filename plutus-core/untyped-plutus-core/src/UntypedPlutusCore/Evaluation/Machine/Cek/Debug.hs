{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all -fforce-recomp -dumpdir /tmp/dumps #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Debug where

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Builtin
import PlutusCore.Default

import GHC.Exts (inline)

toBuiltinsRuntimeDef
    :: (cost ~ CostingPart uni fun, uni ~ DefaultUni, fun ~ DefaultFun)
    => cost -> BuiltinsRuntime fun (CekValue uni fun)
toBuiltinsRuntimeDef = inline toBuiltinsRuntime
