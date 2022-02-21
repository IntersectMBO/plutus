{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -O2 #-}

-- | This module defines a 'ToBuiltinsRuntime' instance for 'CekValue'. It must be the only thing
-- that this module defines. The idea is that dumping the Core of this module gives you the whole
-- builtins machinery compiled (and specialized to 'CekValue') and nothing else. There's no other
-- way to observe what actually happens during evaluation of a builtin application and how the
-- different parts of the builtins machinery interact with each other.
module UntypedPlutusCore.Evaluation.Machine.Cek.Default () where

import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import PlutusCore.Builtin
import PlutusCore.Default

instance ToBuiltinsRuntime DefaultFun (CekValue DefaultUni DefaultFun)
