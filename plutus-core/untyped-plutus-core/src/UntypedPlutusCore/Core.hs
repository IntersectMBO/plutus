{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Core
  ( module Export
  , splitParams
  , splitApplication
  ) where

import UntypedPlutusCore.Core.Instance as Export
import UntypedPlutusCore.Core.Plated as Export
import UntypedPlutusCore.Core.Type as Export

import Data.Bifunctor

-- | Strips off lambda binders.
splitParams :: Term name uni fun a -> ([(name, a)], Term name uni fun a)
splitParams = \case
  LamAbs a n t -> first ((n, a) :) (splitParams t)
  t -> ([], t)

-- | Strip off arguments
splitApplication :: Term name uni fun a -> (Term name uni fun a, [(a, Term name uni fun a)])
splitApplication = go []
  where
    go acc = \case
      Apply ann fun arg -> go ((ann, arg) : acc) fun
      t -> (t, acc)
