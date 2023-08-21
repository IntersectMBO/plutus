{-# LANGUAGE TemplateHaskell #-}
module PlutusCore.Compiler (
    compileTerm
    , compileProgram
    , CompilationOpts (..)
    , coSimplifyOpts
    , defaultCompilationOpts
    ) where

import PlutusCore.Compiler.Erase
import PlutusCore.Compiler.Types
import PlutusCore.Core
import PlutusCore.Name
import PlutusCore.Rename
import UntypedPlutusCore.Core qualified as UPLC
import UntypedPlutusCore.Simplify qualified as UPLC

import Control.Lens
import Control.Monad.Reader

newtype CompilationOpts name a = CompilationOpts { _coSimplifyOpts :: UPLC.SimplifyOpts name a }
  deriving stock (Show)

makeLenses ''CompilationOpts

defaultCompilationOpts :: CompilationOpts name a
defaultCompilationOpts = CompilationOpts { _coSimplifyOpts = UPLC.defaultSimplifyOpts }

-- | Compile a PLC term to UPLC, and optimize it.
compileTerm
    :: (Compiling m uni fun name, MonadReader (CompilationOpts name a) m)
    => Term tyname name uni fun a
    -> m (UPLC.Term name uni fun a)
compileTerm t = do
    simplOpts <- asks _coSimplifyOpts
    let erased =  eraseTerm t
    renamed <- rename erased
    UPLC.simplifyTerm simplOpts renamed

-- | Compile a PLC program to UPLC, and optimize it.
compileProgram
    :: (Compiling m uni fun name, MonadReader (CompilationOpts name a) m)
    => Program tyname name uni fun a
    -> m (UPLC.Program name uni fun a)
compileProgram (Program a v t) = UPLC.Program a v <$> compileTerm t
