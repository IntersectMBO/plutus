{-# LANGUAGE TemplateHaskell #-}

module PlutusCore.Compiler.Opts
  ( CompilationOpts (..)
  , coOptimizeOpts
  , coBuiltinSemanticsVariant
  , defaultCompilationOpts
  ) where

import Control.Lens (makeLenses)
import Data.Default.Class (Default (def))
import PlutusCore.Builtin.Meaning (BuiltinSemanticsVariant)
import UntypedPlutusCore.Optimize.Opts (OptimizeOpts, defaultOptimizeOpts)

data CompilationOpts name fun a = CompilationOpts
  { _coOptimizeOpts :: OptimizeOpts name a
  , _coBuiltinSemanticsVariant :: BuiltinSemanticsVariant fun
  }

$(makeLenses ''CompilationOpts)

defaultCompilationOpts :: Default (BuiltinSemanticsVariant fun) => CompilationOpts name fun a
defaultCompilationOpts =
  CompilationOpts
    { _coOptimizeOpts = defaultOptimizeOpts
    , _coBuiltinSemanticsVariant = def
    }
