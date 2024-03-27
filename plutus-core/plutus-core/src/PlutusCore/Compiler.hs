module PlutusCore.Compiler
  ( module Opts
  , compileTerm
  , compileProgram
  ) where

import PlutusCore.Compiler.Erase
import PlutusCore.Compiler.Types
import PlutusCore.Core
import PlutusCore.Name.Unique
import PlutusCore.Rename
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Simplify qualified as UPLC

import Control.Lens (view)
import Control.Monad.Reader (MonadReader)
import PlutusCore.Compiler.Opts as Opts

-- | Compile a PLC term to UPLC, and optimize it.
compileTerm
  :: (Compiling m uni fun name a, MonadReader (CompilationOpts name fun a) m)
  => Term tyname name uni fun a
  -> m (UPLC.Term name uni fun a)
compileTerm t = do
  simplOpts <- view coSimplifyOpts
  builtinSemanticsVariant <- view coBuiltinSemanticsVariant
  let erased = eraseTerm t
  renamed <- rename erased
  UPLC.simplifyTerm simplOpts builtinSemanticsVariant renamed

-- | Compile a PLC program to UPLC, and optimize it.
compileProgram
  :: (Compiling m uni fun name a, MonadReader (CompilationOpts name fun a) m)
  => Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a)
compileProgram (Program a v t) = UPLC.Program a v <$> compileTerm t
