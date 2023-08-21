{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import PlutusCore.Builtin
import PlutusCore.Name
import PlutusCore.Quote

type Compiling m uni fun name =
  (ToBuiltinMeaning uni fun, MonadQuote m, HasUnique name TermUnique, Ord name)
