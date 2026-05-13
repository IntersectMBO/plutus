{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module UntypedPlutusCore.Contexts where

import PlutusCore.Arity
import UntypedPlutusCore.Core (Term (..))
import UntypedPlutusCore.Core.Instance.Eq ()

-- | A context for an iterated term/type application.
data AppCtx name uni fun a
  = AppCtxTerm a (Term name uni fun a) (AppCtx name uni fun a)
  | AppCtxType a (AppCtx name uni fun a)
  | AppCtxEnd

{-| Takes a term and views it as a head plus an 'AppCtx', e.g.
@
  [{ f t } u v]
  -->
  (f, [{ _ t } u v])
  ==
  f (AppCtxType t (AppCtxTerm u (AppCtxTerm v AppCtxEnd)))
@ -}
splitAppCtx :: Term nam uni fun a -> (Term nam uni fun a, AppCtx nam uni fun a)
splitAppCtx = go AppCtxEnd
  where
    go appCtx = \case
      Apply ann function arg -> go (AppCtxTerm ann arg appCtx) function
      Force ann forcedTerm -> go (AppCtxType ann appCtx) forcedTerm
      term -> (term, appCtx)

-- | Fills in the hole in an 'AppCtx', the inverse of 'splitAppCtx'.
fillAppCtx
  :: Term name uni fun ann
  -> AppCtx name uni fun ann
  -> Term name uni fun ann
fillAppCtx term = \case
  AppCtxEnd -> term
  AppCtxTerm ann arg ctx -> fillAppCtx (Apply ann term arg) ctx
  AppCtxType ann ctx -> fillAppCtx (Force ann term) ctx

data Saturation = Oversaturated | Undersaturated | Saturated

-- | Do the given arguments saturate the given arity?
saturates :: AppCtx name uni fun a -> Arity -> Maybe Saturation
-- Exactly right
saturates AppCtxEnd [] = Just Saturated
-- Parameters left - undersaturated
saturates AppCtxEnd _ = Just Undersaturated
-- Match a term parameter to a term arg
saturates (AppCtxTerm _ _ ctx) (TermParam : arities) = saturates ctx arities
-- Match a type parameter to a type arg
saturates (AppCtxType _ ctx) (TypeParam : arities) = saturates ctx arities
-- Param/arg mismatch
saturates (AppCtxTerm {}) (TypeParam : _) = Nothing
saturates (AppCtxType {}) (TermParam : _) = Nothing
-- Arguments left - undersaturated
saturates (AppCtxTerm {}) [] = Just Oversaturated
saturates (AppCtxType {}) [] = Just Oversaturated
