{-# LANGUAGE PatternSynonyms #-}

{-|
Transform multi-argument applications into case-constr form.

This is essentially the reverse of 'CaseReduce'. An application of 3 or more
arguments, e.g., @f x y z@ is rewritten to @case (constr 0 [x, y, z]) [f]@,
which is cheaper, and smaller in AST size, though it is sometimes slightly
bigger in cbor size.

I cannot think of any case where this pass could enable further optimizations.
It can certainly destroy optimization opportunities, similar to CSE.
So it should only be run once, at the very end of the pipeline. CSE is also
run at the end, but it runs for multiple iterations interleaved with other
optimizations, because CSE can both destroy and enable further optimizations. -}
module UntypedPlutusCore.Transform.ApplyToCase (applyToCase) where

import Control.Lens (over)
import Data.Vector qualified as V
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Optimizer
  ( OptimizerT
  , recordOptimization
  , pattern ApplyToCaseStage
  )

minArgs :: Int
minArgs = 3
{-# INLINE minArgs #-}

applyToCase
  :: Monad m
  => Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
applyToCase term = do
  let result = processTerm term
  recordOptimization term ApplyToCaseStage result
  pure result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm t = case splitApplication t of
  (fun, args)
    | length args >= minArgs ->
        let ann = termAnn t
         in Case ann (Constr ann 0 (processTerm . snd <$> args)) (V.singleton (processTerm fun))
  _ -> over termSubterms processTerm t
