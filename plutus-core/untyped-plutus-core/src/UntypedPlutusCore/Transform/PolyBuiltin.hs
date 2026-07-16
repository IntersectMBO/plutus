{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-| Hoist fully-forced polymorphic builtins.

Before: @...force (force fstPair)...@
After: @(\fstPairForced -> ...fstPairForced...) (force (force fstPair))@ -}
module UntypedPlutusCore.Transform.PolyBuiltin
  ( polyBuiltin
  ) where

import PlutusCore (Name, getAnn)
import PlutusCore.Arity (Param (..), builtinArity)
import PlutusCore.Builtin (ToBuiltinMeaning (BuiltinSemanticsVariant))
import PlutusCore.Quote (MonadQuote, freshName)
import UntypedPlutusCore.Core.Plated (termSubterms, termSubtermsDeep)
import UntypedPlutusCore.Core.Type (Term (..))
import UntypedPlutusCore.Transform.Optimizer
  ( OptimizerT
  , recordOptimization
  , pattern PolyBuiltinStage
  )

import Control.Lens (foldlOf', transformOf)
import Data.Foldable qualified as F
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
import Data.Hashable (Hashable)
import Data.Proxy (Proxy (..))
import Data.Traversable (for)

polyBuiltin
  :: forall m uni fun pat a
   . ( MonadQuote m
     , Hashable fun
     , ToBuiltinMeaning uni fun
     )
  => BuiltinSemanticsVariant fun
  -> Term Name uni fun pat a
  -> OptimizerT Name uni fun pat a m (Term Name uni fun pat a)
polyBuiltin semvar term = do
  let numForces :: fun -> Int
      numForces = length . takeWhile (== TypeParam) . builtinArity (Proxy @uni) semvar

      -- If it is a fully forced polymorphic builtin, return `Just (ann, fun, number of forces)`.
      checkFullyForced :: Term Name uni fun pat a -> Maybe (a, fun, Int)
      checkFullyForced t = case t' of
        Builtin _ fun
          | n >= 1
          , n == numForces fun ->
              Just (getAnn t, fun, n)
        _ -> Nothing
        where
          (n, t') = peelForces t

      candidates :: HashMap fun Int
      candidates =
        foldlOf' termSubtermsDeep alg Map.empty term
        where
          alg !acc t = case checkFullyForced t of
            Just (_, fun, n) -> Map.insert fun n acc
            Nothing -> acc

  result <-
    if Map.null candidates
      then pure term
      else do
        named <- for (Map.toList candidates) $ \(fun, n) -> do
          name <- freshName "forced"
          pure (fun, (name, n))
        let binders = Map.fromList named
            subst t = case checkFullyForced t of
              Just (ann, fun, _)
                | Just (name, _) <- Map.lookup fun binders ->
                    Var ann name
              _ -> t
            rewritten = transformOf termSubterms subst term
        pure $ wrap (getAnn term) named rewritten

  recordOptimization term PolyBuiltinStage result
  pure result

peelForces :: Term name uni fun pat a -> (Int, Term name uni fun pat a)
peelForces = go 0
  where
    go !k (Force _ t) = go (k + 1) t
    go !k t = (k, t)

wrap
  :: forall uni fun pat a
   . a
  -> [(fun, (Name, Int))]
  -> Term Name uni fun pat a
  -> Term Name uni fun pat a
wrap ann entries body =
  let lams = foldr (\(_, (name, _)) -> LamAbs ann name) body entries
   in F.foldl'
        (\acc (fun, (_, n)) -> Apply ann acc (applyForces n (Builtin ann fun)))
        lams
        entries
  where
    applyForces :: Int -> Term Name uni fun pat a -> Term Name uni fun pat a
    applyForces 0 = id
    applyForces n = applyForces (n - 1) . Force ann
