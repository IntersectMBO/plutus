module PlutusCore.Compiler.Erase (eraseTerm, eraseProgram) where

import Data.Vector (fromList)
import PlutusCore.Core
import UntypedPlutusCore.Core qualified as UPLC

-- | Erase a Typed Plutus Core term to its untyped counterpart.
eraseTerm :: Term tyname name uni fun ann -> UPLC.Term name uni fun ann
eraseTerm (Var ann name)           = UPLC.Var ann name
eraseTerm (TyAbs ann _ _ body)     = UPLC.Delay ann (eraseTerm body)
eraseTerm (LamAbs ann name _ body) = UPLC.LamAbs ann name (eraseTerm body)
eraseTerm (Apply ann fun arg)      = UPLC.Apply ann (eraseTerm fun) (eraseTerm arg)
eraseTerm (Constant ann con)       = UPLC.Constant ann con
eraseTerm (Builtin ann bn)         = UPLC.Builtin ann bn
eraseTerm (TyInst ann term _)      = UPLC.Force ann (eraseTerm term)
eraseTerm (Unwrap _ term)          = eraseTerm term
eraseTerm (IWrap _ _ _ term)       = eraseTerm term
eraseTerm (Error ann _)            = UPLC.Error ann
eraseTerm (Constr ann _ i args)    = UPLC.Constr ann i (fromList $ fmap eraseTerm args)
eraseTerm (Case ann _ arg cs)      = UPLC.Case ann (eraseTerm arg) (fromList $ fmap eraseTerm cs)

eraseProgram :: Program tyname name uni fun ann -> UPLC.Program name uni fun ann
eraseProgram (Program a v t) = UPLC.Program a v $ eraseTerm t
