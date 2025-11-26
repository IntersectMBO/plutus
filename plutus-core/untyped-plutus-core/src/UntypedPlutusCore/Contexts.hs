{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Contexts where

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
      Apply ann function argument -> go (AppCtxTerm ann argument appCtx) function
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
