module PlutusCore.Compiler.Erase
  ( eraseTerm
  , eraseProgram
  , eraseTermWithSemantics
  , eraseProgramWithSemantics
  ) where

import PlutusPrelude

import Data.Vector (fromList)
import PlutusCore.Builtin.Meaning
import PlutusCore.Core
import UntypedPlutusCore.Core qualified as UPLC

-- | Erase a Typed Plutus Core term using the default builtin semantics.
eraseTerm
  :: ToBuiltinMeaning uni fun
  => Term tyname name uni fun ann
  -> UPLC.Term name uni fun ann
eraseTerm = eraseTermWithSemantics def

eraseProgram
  :: ToBuiltinMeaning uni fun
  => Program tyname name uni fun ann
  -> UPLC.Program name uni fun ann
eraseProgram (Program a v t) = UPLC.Program a v $ eraseTerm t

{-| Erase a Typed Plutus Core term using an explicit builtin semantics variant, reifying hidden
term arguments encoded by type-directed builtin applications. -}
eraseTermWithSemantics
  :: ToBuiltinMeaning uni fun
  => BuiltinSemanticsVariant fun
  -> Term tyname name uni fun ann
  -> UPLC.Term name uni fun ann
eraseTermWithSemantics semvar = go
  where
    go (Var ann name) = UPLC.Var ann name
    go (TyAbs ann _ _ body) = UPLC.Delay ann (go body)
    go (LamAbs ann name _ body) = UPLC.LamAbs ann name (go body)
    go (Apply ann fun arg) = UPLC.Apply ann (go fun) (go arg)
    go (Constant ann con) = UPLC.Constant ann con
    go (Builtin ann bn) = UPLC.Builtin ann bn
    go (TyInst ann (Builtin builtinAnn fun) ty)
      | Just typeApplication <- toBuiltinTypeApplication semvar fun =
          case btaReifyArgument typeApplication ty of
            Left err -> error $ "Invalid type-directed builtin application after typechecking: " <> show err
            Right hiddenArg ->
              UPLC.Apply
                ann
                (UPLC.Builtin builtinAnn fun)
                (UPLC.Constant ann hiddenArg)
    go (TyInst ann term _) = UPLC.Force ann (go term)
    go (Unwrap _ term) = go term
    go (IWrap _ _ _ term) = go term
    go (Error ann _) = UPLC.Error ann
    go (Constr ann _ i args) = UPLC.Constr ann i (fmap go args)
    go (Case ann _ arg cs) = UPLC.Case ann (go arg) (fromList $ fmap go cs)

eraseProgramWithSemantics
  :: ToBuiltinMeaning uni fun
  => BuiltinSemanticsVariant fun
  -> Program tyname name uni fun ann
  -> UPLC.Program name uni fun ann
eraseProgramWithSemantics semvar (Program ann version term) =
  UPLC.Program ann version $ eraseTermWithSemantics semvar term
