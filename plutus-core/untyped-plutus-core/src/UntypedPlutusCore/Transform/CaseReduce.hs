{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

module UntypedPlutusCore.Transform.CaseReduce
  ( caseReduce
  , processTerm
  ) where

import Control.Lens (mapAccumLOf)
import Data.Bifunctor (second)
import Data.Vector qualified as V
import PlutusCore.Builtin (CaseBuiltin (..))
import PlutusCore.MkPlc
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Optimizer
  ( OptimizerT
  , recordOptimization
  , pattern CaseReduceStage
  )

caseReduce
  :: (Monad m, CaseBuiltin uni)
  => Term name uni fun pat a
  -> OptimizerT name uni fun pat a m (Term name uni fun pat a)
caseReduce term = do
  let result = snd $ processTermWithMatch term
  recordOptimization term CaseReduceStage result
  return result

processTermWithMatch
  :: CaseBuiltin uni
  => Term name uni fun pat a
  -> (Bool, Term name uni fun pat a)
processTermWithMatch term =
  let (childHasMatch, term') = mapAccumLOf termSubterms processChild False term
      hasMatch = isMatch term || childHasMatch
   in (hasMatch, if hasMatch then term' else processTerm term')
  where
    processChild found child =
      let (childHasMatch, child') = processTermWithMatch child
       in (found || childHasMatch, child')

    isMatch Match {} = True
    isMatch _ = False

processTerm
  :: CaseBuiltin uni
  => Term name uni fun pat a
  -> Term name uni fun pat a
processTerm term = case term of
  -- We could've rewritten those patterns as 'Error' in the 'Nothing' cases, but that would turn a
  -- structural error into an operational one, which would be unfortunate, so instead we decided
  -- not to fully optimize such scripts, since they aren't valid anyway.
  Case ann (Constr _ i args) cs
    | Just c <- (V.!?) cs (fromIntegral i) ->
        mkIterApp c ((ann,) <$> args)
  Case ann (Constant _ con) cs
    | Right t <- headSpineToTerm ann (second (Constant ann) (caseBuiltin con cs)) -> t
  t -> t

-- A match in a branch can fail after an early argument. The original 'Constr' evaluates all fields
-- before branch selection, so 'processTermWithMatch' skips only the enclosing rewrite while still
-- optimizing independent children in one bottom-up traversal.
