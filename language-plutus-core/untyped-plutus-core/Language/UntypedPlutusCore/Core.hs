module Language.UntypedPlutusCore.Core where

import qualified Language.PlutusCore.Core     as PLC
import           Language.PlutusCore.Universe

data Term name uni ann
    = Constant ann (Some (ValueOf uni))
    | Builtin ann (PLC.Builtin ann)
    | Var ann name
    | LamAbs ann name (Term name uni ann)
    | Apply ann (Term name uni ann) (Term name uni ann)
    | Delay ann (Term name uni ann)
    | Force ann (Term name uni ann)
    | Error ann

erase :: PLC.Term tyname name uni ann -> Term name uni ann
erase (PLC.Var ann name)           = Var ann name
erase (PLC.TyAbs ann _ _ body)     = Delay ann (erase body)
erase (PLC.LamAbs ann name _ body) = LamAbs ann name (erase body)
erase (PLC.Apply ann fun arg)      = Apply ann (erase fun) (erase arg)
erase (PLC.Constant ann con)       = Constant ann con
erase (PLC.Builtin ann bn)         = Builtin ann bn
erase (PLC.TyInst ann term _)      = Force ann (erase term)
erase (PLC.Unwrap _ term)          = erase term
erase (PLC.IWrap _ _ _ term)       = erase term
erase (PLC.Error ann _)            = Error ann
