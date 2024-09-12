module PlutusCore.Compiler
  ( module Opts
  , compileTerm
  , compileProgram
  , runCompile
  , evalCompile
  ) where

import PlutusCore.Compiler.Erase
import PlutusCore.Compiler.Opts as Opts
import PlutusCore.Compiler.Types
import PlutusCore.Core
import PlutusCore.Name.Unique
import PlutusCore.Rename
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Simplify qualified as UPLC

import Control.Lens (view)
import Control.Monad.Reader (MonadReader, ReaderT (runReaderT))
import Control.Monad.State (MonadState (..), StateT (runStateT))

-- | Compile a PLC term to UPLC, and optimize it.
compileTerm
  :: (Compiling m uni fun name a
  , MonadReader (CompilationOpts name fun a) m
  , MonadState (UPLCSimplifierTrace name uni fun a) m
  )
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
  :: (Compiling m uni fun name a
  , MonadReader (CompilationOpts name fun a) m
  , MonadState (UPLCSimplifierTrace name uni fun a) m
  )
  => Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a)
compileProgram (Program a v t) = UPLC.Program a v <$> compileTerm t

type Compile m name uni fun a =
  ReaderT
    (CompilationOpts name fun a)
    (StateT
       (UPLCSimplifierTrace name uni fun a)
       m
    )

runCompile
  :: CompilationOpts name fun a
  -> Compile m name uni fun a b
  -> m (b, UPLCSimplifierTrace name uni fun a)
runCompile opts =
  flip runStateT initUPLCSimplifierTrace
  . flip runReaderT opts

evalCompile
  :: Functor m
  => CompilationOpts name fun a
  -> Compile m name uni fun a b
  -> m b
evalCompile opts = fmap fst . runCompile opts
