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

-- | An argument consists of an annotation and a `Term`. The annotation should be
-- used when constructing an `Apply` node.
data Arg name uni fun a = Arg a (Term name uni fun a)

-- | Strip off arguments
splitApplication :: Term name uni fun a -> (Term name uni fun a, [Arg name uni fun a])
splitApplication = go []
  where
    go acc = \case
      Apply ann fun arg -> go (Arg ann arg : acc) fun
      t                 -> (t, acc)

-- | Make an Apply node from the given function and arguments.
mkApplication :: Term name uni fun a -> [Arg name uni fun a] -> Term name uni fun a
mkApplication = foldl' $ \acc (Arg ann arg) -> Apply ann acc arg
