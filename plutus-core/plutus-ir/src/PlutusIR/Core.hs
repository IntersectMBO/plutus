module PlutusIR.Core (
    module Export,
    Arg (..),
    collectArgs,
    mkTermApps,
) where

import Data.List (foldl')

import PlutusIR.Core.Instance ()
import PlutusIR.Core.Plated as Export
import PlutusIR.Core.Type as Export

data Arg tyname name uni fun ann
    = TermArg (Term tyname name uni fun ann)
    | TypeArg (Type tyname uni ann)

-- | Takes a nested application and returns the function and the arguments.
collectArgs ::
    Term tyname name uni fun ann ->
    (Term tyname name uni fun ann, [(Arg tyname name uni fun ann, ann)])
collectArgs t = go t []
  where
    go (Apply ann f a) as  = go f ((TermArg a, ann) : as)
    go (TyInst ann f a) as = go f ((TypeArg a, ann) : as)
    go other as            = (other, as)

-- | Apply a list of arguments to a function.
mkTermApps ::
    Term tyname name uni fun ann ->
    [(Arg tyname name uni fun ann, ann)] ->
    Term tyname name uni fun ann
mkTermApps = foldl' $ \acc (arg, ann) -> case arg of
    TermArg t  -> Apply ann acc t
    TypeArg ty -> TyInst ann acc ty
