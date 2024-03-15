module AnyProgram.Apply
    ( applyProgram
    ) where

import Types
import GetOpt
import AnyProgram.With

import PlutusCore qualified as PLC
import PlutusIR qualified as PIR
import UntypedPlutusCore qualified as UPLC
import PlutusCore.Error as PLC

import Control.Monad.Except

-- | Given a singleton witness and two programs of that type witness, apply them together.
--
applyProgram :: (?opts :: Opts, MonadError PLC.ApplyProgramError m)
             => SLang s -> FromLang s -> FromLang s -> m (FromLang s)
applyProgram _ _ _ | _wholeOpt ?opts = error "error FIXME: not implemented yet"
applyProgram sng p1 p2 = withSemigroupA (_sann sng) $
    case sng of
        SPir{} -> PIR.applyProgram p1 p2
        SPlc{} -> PLC.applyProgram p1 p2
        SUplc{} -> UPLC.UnrestrictedProgram <$> UPLC.applyProgram (UPLC.unUnrestrictedProgram p1) (UPLC.unUnrestrictedProgram p2)
        SData{} -> error "FIXME: not implemented yet"
