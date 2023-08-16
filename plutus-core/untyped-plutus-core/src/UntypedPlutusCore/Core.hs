{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Core (
  module Export,
  splitApplication,
) where

import UntypedPlutusCore.Core.Instance as Export
import UntypedPlutusCore.Core.Plated as Export
import UntypedPlutusCore.Core.Type as Export

-- | Strip off arguments
splitApplication :: Term name uni fun a -> (Term name uni fun a, [(a, Term name uni fun a)])
splitApplication = go []
  where
    go acc = \case
      Apply ann fun arg -> go ((ann, arg) : acc) fun
      t                 -> (t, acc)
