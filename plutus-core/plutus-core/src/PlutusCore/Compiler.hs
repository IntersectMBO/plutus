module PlutusCore.Compiler
  ( module UntypedPlutusCore.Optimize.Opts
  , compileTerm
  , compileProgram
  , compileProgramWithTrace
  ) where

import PlutusCore.Compiler.Erase
import PlutusCore.Compiler.Types
import PlutusCore.Core
import PlutusCore.Name.Unique
import PlutusCore.Rename
import UntypedPlutusCore.Analysis.Builtins
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Optimize qualified as UPLC
import UntypedPlutusCore.Optimize.Opts

import Control.Lens (view)
import Control.Monad.Reader (MonadReader)

-- | Compile a PLC term to UPLC, and optimize it.
compileTerm
  :: ( Compiling m uni fun name a
     , MonadReader (OptimizeOpts name uni fun a) m
     )
  => Term tyname name uni fun a
  -> m (UPLC.Term name uni fun a)
compileTerm t = do
  builtinSemanticsVariant <- view (ooBuiltinsInfo . biSemanticsVariant)
  let erased = eraseTerm t
  renamed <- rename erased
  optimizeOpts <- view id
  UPLC.optimizeTerm optimizeOpts builtinSemanticsVariant renamed

-- | Compile a PLC program to UPLC, and optimize it.
compileProgram
  :: ( Compiling m uni fun name a
     , MonadReader (OptimizeOpts name uni fun a) m
     )
  => Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a)
compileProgram (Program a v t) = UPLC.Program a v <$> compileTerm t

{-| Compile a PLC program to UPLC, and optimize it. This includes
the compilation trace in the result. -}
compileProgramWithTrace
  :: ( Compiling m uni fun name a
     , MonadReader (OptimizeOpts name uni fun a) m
     )
  => Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a, UPLC.OptimizerTrace name uni fun a)
compileProgramWithTrace (Program a v t) = do
  builtinSemanticsVariant <- view (ooBuiltinsInfo . biSemanticsVariant)
  let erased = eraseTerm t
  renamedProgram <- UPLC.Program a v <$> rename erased
  optimizeOpts <- view id
  UPLC.optimizeProgramWithTrace
    optimizeOpts
    builtinSemanticsVariant
    renamedProgram
