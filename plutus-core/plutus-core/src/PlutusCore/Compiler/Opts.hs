{-# LANGUAGE TemplateHaskell #-}

module PlutusCore.Compiler.Opts
  ( CompilationOpts (..)
  , coSimplifyOpts
  , coBuiltinSemanticsVariant
  , defaultCompilationOpts
  ) where

import Control.Lens (makeLenses)
import Data.Default.Class (Default (def))
import PlutusCore.Builtin.Meaning (BuiltinSemanticsVariant)
import UntypedPlutusCore.Simplify.Opts (SimplifyOpts, defaultSimplifyOpts)

data CompilationOpts name fun a = CompilationOpts
  { _coSimplifyOpts :: SimplifyOpts name a
  , _coBuiltinSemanticsVariant :: BuiltinSemanticsVariant fun
  }

$(makeLenses ''CompilationOpts)

defaultCompilationOpts :: Default (BuiltinSemanticsVariant fun) => CompilationOpts name fun a
defaultCompilationOpts =
  CompilationOpts
    { _coSimplifyOpts = defaultSimplifyOpts
    , _coBuiltinSemanticsVariant = def
    }
