{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

module PlutusIR.Transform.RewriteRules.CancelIfThenTrueElseFalse
  ( rewriteRuleCancelIfThenTrueElseFalse
  ) where

import PlutusCore (someValue)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusIR.Core.Type (Term (Constant), Type (TyBuiltin))
import PlutusIR.Transform.RewriteRules.Common (pattern A, pattern B, pattern I)

rewriteRuleCancelIfThenTrueElseFalse
  :: Term ty name DefaultUni DefaultFun a
  -> Term ty name DefaultUni DefaultFun a
rewriteRuleCancelIfThenTrueElseFalse = \case
  B Builtin.IfThenElse `I` TyBuiltin _ _ `A` p `A` Constant _ t `A` Constant _ e
    | t == someValue True && e == someValue False -> p
  term -> term
