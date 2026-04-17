module PlutusCore.Compiler
  ( module Opts
  , compileTerm
  , compileProgram
  , compileProgramWithTrace
  ) where

import PlutusCore.Builtin (CostingPart)
import PlutusCore.Compiler.Erase
import PlutusCore.Compiler.Opts as Opts
import PlutusCore.Compiler.Types
import PlutusCore.Core
import PlutusCore.Name.Unique
import PlutusCore.Rename
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Optimize qualified as UPLC

import Control.Lens (view)
import Control.Monad.Reader (MonadReader)

-- | Compile a PLC term to UPLC, and optimize it.
compileTerm
  :: ( Compiling m uni fun name a
     , MonadReader (CompilationOpts name fun a) m
     )
  => CostingPart uni fun
  -> Term tyname name uni fun a
  -> m (UPLC.Term name uni fun a)
compileTerm costingPart t = do
  optimizeOpts <- view coOptimizeOpts
  builtinSemanticsVariant <- view coBuiltinSemanticsVariant
  let erased = eraseTerm t
  renamed <- rename erased
  UPLC.optimizeTerm optimizeOpts builtinSemanticsVariant costingPart renamed

-- | Compile a PLC program to UPLC, and optimize it.
compileProgram
  :: ( Compiling m uni fun name a
     , MonadReader (CompilationOpts name fun a) m
     )
  => CostingPart uni fun
  -> Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a)
compileProgram costingPart (Program a v t) = UPLC.Program a v <$> compileTerm costingPart t

{-| Compile a PLC program to UPLC, and optimize it. This includes
the compilation trace in the result. -}
compileProgramWithTrace
  :: ( Compiling m uni fun name a
     , MonadReader (CompilationOpts name fun a) m
     )
  => CostingPart uni fun
  -> Program tyname name uni fun a
  -> m (UPLC.Program name uni fun a, UPLC.OptimizerTrace name uni fun a)
compileProgramWithTrace costingPart (Program a v t) = do
  optimizeOpts <- view coOptimizeOpts
  builtinSemanticsVariant <- view coBuiltinSemanticsVariant
  let erased = eraseTerm t
  renamedProgram <- UPLC.Program a v <$> rename erased
  UPLC.optimizeProgramWithTrace
    optimizeOpts
    builtinSemanticsVariant
    costingPart
    renamedProgram
