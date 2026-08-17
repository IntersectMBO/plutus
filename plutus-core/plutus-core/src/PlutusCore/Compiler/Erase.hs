module PlutusCore.Compiler.Erase
  ( eraseTerm
  , eraseProgram
  , eraseTermWithSemantics
  , eraseProgramWithSemantics
  ) where

import Data.Vector (fromList)
import PlutusCore.Builtin.Meaning
import PlutusCore.Core
import UntypedPlutusCore.Core qualified as UPLC

-- | Erase a Typed Plutus Core term.
eraseTerm
  :: Term tyname name uni fun ann
  -> UPLC.Term name uni fun ann
eraseTerm = go
  where
    go (Var ann name) = UPLC.Var ann name
    go (TyAbs ann _ _ body) = UPLC.Delay ann (go body)
    go (LamAbs ann name _ body) = UPLC.LamAbs ann name (go body)
    go (Apply ann fun arg) = UPLC.Apply ann (go fun) (go arg)
    go (Constant ann con) = UPLC.Constant ann con
    go (Builtin ann bn) = UPLC.Builtin ann bn
    go (BuiltinRep ann _ con) = UPLC.Constant ann con
    go (TyInst ann term _) = UPLC.Force ann (go term)
    go (Unwrap _ term) = go term
    go (IWrap _ _ _ term) = go term
    go (Error ann _) = UPLC.Error ann
    go (Constr ann _ i args) = UPLC.Constr ann i (fmap go args)
    go (Case ann _ arg cs) = UPLC.Case ann (go arg) (fromList $ fmap go cs)

eraseProgram
  :: Program tyname name uni fun ann
  -> UPLC.Program name uni fun ann
eraseProgram (Program a v t) = UPLC.Program a v $ eraseTerm t

-- | Compatibility wrapper for callers that already carry an explicit builtin semantics variant.
eraseTermWithSemantics
  :: BuiltinSemanticsVariant fun
  -> Term tyname name uni fun ann
  -> UPLC.Term name uni fun ann
eraseTermWithSemantics _semvar = eraseTerm

eraseProgramWithSemantics
  :: BuiltinSemanticsVariant fun
  -> Program tyname name uni fun ann
  -> UPLC.Program name uni fun ann
eraseProgramWithSemantics semvar (Program ann version term) =
  UPLC.Program ann version $ eraseTermWithSemantics semvar term
