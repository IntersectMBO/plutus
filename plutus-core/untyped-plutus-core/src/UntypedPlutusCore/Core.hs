{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Core (
  module Export,
  splitParams,
  splitApplication,
  splitForces,
) where

import UntypedPlutusCore.Core.Instance as Export
import UntypedPlutusCore.Core.Plated as Export
import UntypedPlutusCore.Core.Type as Export

import Data.Bifunctor

-- | Strips off lambda binders.
splitParams :: Term name uni fun a -> ([name], Term name uni fun a)
splitParams = \case
  LamAbs _ n t -> first (n :) (splitParams t)
  t            -> ([], t)

-- | Strip off arguments
splitApplication :: Term name uni fun a -> (Term name uni fun a, [(a, Term name uni fun a)])
splitApplication = go []
  where
    go acc = \case
      Apply ann fun arg -> go ((ann, arg) : acc) fun
      t                 -> (t, acc)

-- | Extract the term inside a number of nested `Force` nodes.
--
-- This also returns the annotations on the `Force` noes, in the order of outer to inner.
splitForces :: Term name uni fun a -> (Term name uni fun a, [a])
splitForces = \case
  Force ann body -> second (ann:) (splitForces body)
  t              -> (t, [])
