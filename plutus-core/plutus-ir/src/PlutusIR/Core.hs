module PlutusIR.Core (
    module Export,
    Expr (..),
    collectArgs,
    mkTermApps,
) where

import Data.List (foldl')

import PlutusIR.Core.Instance ()
import PlutusIR.Core.Plated as Export
import PlutusIR.Core.Type as Export

data Expr tyname name uni fun ann
    = TermExpr (Term tyname name uni fun ann)
    | TypeExpr (Type tyname uni ann)

-- | Takes a nested application and returns the function and the arguments.
collectArgs ::
    Term tyname name uni fun ann ->
    (Term tyname name uni fun ann, [(Expr tyname name uni fun ann, ann)])
collectArgs expr = go expr []
  where
    go (Apply ann f a) as  = go f ((TermExpr a, ann) : as)
    go (TyInst ann f a) as = go f ((TypeExpr a, ann) : as)
    go other as            = (other, as)

-- | Apply a list of arguments to a function.
mkTermApps ::
    Term tyname name uni fun ann ->
    [(Expr tyname name uni fun ann, ann)] ->
    Term tyname name uni fun ann
mkTermApps = foldl' $ \acc (expr, ann) -> case expr of
    TermExpr t  -> Apply ann acc t
    TypeExpr ty -> TyInst ann acc ty
