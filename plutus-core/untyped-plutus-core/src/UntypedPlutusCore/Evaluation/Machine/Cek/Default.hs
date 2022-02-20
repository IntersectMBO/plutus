{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O2 #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Default () where

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Builtin
import PlutusCore.Default

instance ToBuiltinsRuntime DefaultFun (CekValue DefaultUni DefaultFun)
