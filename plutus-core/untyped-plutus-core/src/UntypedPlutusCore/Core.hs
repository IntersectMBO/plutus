{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Core (
  module Export,
  splitApplication,
  mkApplication,
) where

import UntypedPlutusCore.Core.Instance as Export
import UntypedPlutusCore.Core.Plated as Export
import UntypedPlutusCore.Core.Type as Export

import Data.List (foldl')

type Arg name uni fun a = (Term name uni fun a, a)

-- | Strip off arguments
splitApplication :: Term name uni fun a -> (Term name uni fun a, [Arg name uni fun a])
splitApplication = go []
  where
    go acc = \case
      Apply ann fun arg -> go ((arg, ann) : acc) fun
      t                 -> (t, acc)

-- | Make an Apply node from the given function and arguments.
mkApplication :: Term name uni fun a -> [Arg name uni fun a] -> Term name uni fun a
mkApplication = foldl' $ \acc (arg, ann) -> Apply ann acc arg
