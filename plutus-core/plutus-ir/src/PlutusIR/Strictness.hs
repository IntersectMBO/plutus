{-# LANGUAGE LambdaCase #-}

-- | Strictness analysis.
module PlutusIR.Strictness (isStrictIn) where

import PlutusIR (Binding (TermBind), Strictness (Strict), Term (..))

-- | Whether the given name is strict in the given term.
isStrictIn
  :: forall tyname name uni fun a
   . Eq name
  => name
  -> Term tyname name uni fun a
  -> Bool
isStrictIn n = go
  where
    go = \case
      Var _ n' -> n == n'
      Let _ _ bs body -> any goBinding bs || go body
      Apply _ fun arg -> go fun || go arg
      TyInst _ body _ -> go body
      IWrap _ _ _ body -> go body
      Unwrap _ body -> go body
      Constr _ _ _ args -> any go args
      Case _ _ scrut _ -> go scrut
      TyAbs {} -> False
      LamAbs {} -> False
      Constant {} -> False
      Builtin {} -> False
      Error {} -> False

    goBinding = \case
      TermBind _ Strict _ rhs -> go rhs
      _ -> False
