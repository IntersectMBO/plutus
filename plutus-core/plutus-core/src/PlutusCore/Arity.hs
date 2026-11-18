{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Arity (Param (..), Arity, typeSchemeArity, builtinArity) where

import Data.Proxy
import PlutusCore
import PlutusCore.Builtin

-- | Get the arity of a builtin function from the 'PLC.BuiltinSemanticsVariant'.
builtinArity
  :: forall uni fun
   . ToBuiltinMeaning uni fun
  => Proxy uni
  -> BuiltinSemanticsVariant fun
  -> fun
  -> Arity
builtinArity _ semvar fun =
  case toBuiltinMeaning @uni @fun @(Term TyName Name uni fun ()) semvar fun of
    BuiltinMeaning sch _ _ -> typeSchemeArity sch
