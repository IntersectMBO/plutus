module AnyProgram.Apply
  ( applyProgram
  ) where

import AnyProgram.With
import PlutusCore qualified as PLC
import PlutusCore.Error as PLC
import PlutusIR qualified as PIR
import Types
import UntypedPlutusCore qualified as UPLC

import Control.Monad.Except

-- | Given a singleton witness and two programs of that type witness, apply them together.
applyProgram
  :: MonadError PLC.ApplyProgramError m
  => SLang s -> FromLang s -> FromLang s -> m (FromLang s)
applyProgram sng p1 p2 = withA @Semigroup (_sann sng) $
  case sng of
    SPir {} -> PIR.applyProgram p1 p2
    SPlc {} -> PLC.applyProgram p1 p2
    SUplc {} ->
      UPLC.UnrestrictedProgram
        <$> UPLC.unUnrestrictedProgram p1 `UPLC.applyProgram` UPLC.unUnrestrictedProgram p2
    SData {} -> error "Cannot apply to Data. This should have failed earlier during compilation."
