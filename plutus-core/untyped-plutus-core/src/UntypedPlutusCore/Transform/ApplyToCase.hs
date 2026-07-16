{-# LANGUAGE LambdaCase #-}
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

import Control.Lens (mapAccumLOf)
import Data.List (mapAccumL)
import Data.Vector qualified as V
import PlutusCore.MkPlc (mkIterApp)
import PlutusPrelude (getAnn)
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
  => Term name uni fun pat a
  -> OptimizerT name uni fun pat a m (Term name uni fun pat a)
applyToCase term = do
  let result = processTerm term
  recordOptimization term ApplyToCaseStage result
  pure result

processTerm :: Term name uni fun pat a -> Term name uni fun pat a
processTerm = snd . go
  where
    go term = case splitApplication term of
      (fun, args)
        | length args >= minArgs ->
            let (funHasMatch, fun') = go fun
                (argsHaveMatch, args') = mapAccumL processArg False args
                hasMatch = funHasMatch || argsHaveMatch
                ann = getAnn term
                result
                  | hasMatch = mkIterApp fun' args'
                  | otherwise = Case ann (Constr ann 0 (snd <$> args')) (V.singleton fun')
             in (hasMatch, result)
      _ ->
        let (childHasMatch, term') = mapAccumLOf termSubterms processChild False term
            hasMatch = isMatch term || childHasMatch
         in (hasMatch, term')

    processChild found child =
      let (childHasMatch, child') = go child
       in (found || childHasMatch, child')

    processArg found (ann, arg) =
      let (argHasMatch, arg') = go arg
       in (found || argHasMatch, (ann, arg'))

    isMatch Match {} = True
    isMatch _ = False

-- A 'Match' can fail while evaluating a function or an intermediate application. Moving every
-- argument into a constructor would evaluate later arguments first, so @go@ does not rewrite an
-- application containing one. Splitting the full application spine before descending preserves
-- the original top-down behaviour of this pass, while propagating the flag avoids repeatedly
-- rescanning subtrees.
