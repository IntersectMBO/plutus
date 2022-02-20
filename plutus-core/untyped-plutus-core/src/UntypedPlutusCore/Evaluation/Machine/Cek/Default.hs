{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O2 #-}

{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all -fforce-recomp -dumpdir /tmp/dumps #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Default () where

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Builtin
import PlutusCore.Default

instance ToBuiltinsRuntime DefaultFun (CekValue DefaultUni DefaultFun)
