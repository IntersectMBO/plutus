{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Core
  ( module Export
  , splitParams
  , splitApplication
  , extractBindings
  , wrapWithBindings
  ) where

import UntypedPlutusCore.Core.Instance as Export
import UntypedPlutusCore.Core.Plated as Export
import UntypedPlutusCore.Core.Type as Export

import Data.Bifunctor
import Data.Foldable qualified as F

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

{-| Similar to @PlutusIR.Transform.Beta.extractBindings@, but for UPLC.

[(\x . t) a] -> Just ([(x, a)], t)

[[[(\x . (\y . (\z . t))) a] b] c] -> Just ([(x, a), (y, b), (z, c)]) t)

[[(\x . t) a] b] -> Nothing -}
extractBindings
  :: Term name uni fun a
  -> Maybe ([((name, a), (Term name uni fun a, a))], Term name uni fun a)
extractBindings t = case splitApplication t of
  (_, []) -> Nothing
  (f, args) -> case splitParams f of
    (params, body)
      | length params >= length args ->
          let bindings = zipWith (\(n, la) (aa, arg) -> ((n, la), (arg, aa))) params args
              remainingParams = drop (length args) params
              body' = foldr (\(n, la) -> LamAbs la n) body remainingParams
           in Just (bindings, body')
      | otherwise -> Nothing

-- | The opposite of `extractBindings`.
wrapWithBindings
  :: [((name, a), (Term name uni fun a, a))]
  -> Term name uni fun a
  -> Term name uni fun a
wrapWithBindings bindings body =
  F.foldl'
    (\acc (_, (arg, aa)) -> Apply aa acc arg)
    (foldr (\((n, la), _) -> LamAbs la n) body bindings)
    bindings
