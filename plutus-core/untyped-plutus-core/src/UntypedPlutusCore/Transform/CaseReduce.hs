{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}

module UntypedPlutusCore.Transform.CaseReduce
  ( caseReduce
  , processTerm
  ) where

import Control.Lens (transformOf)
import Data.Bifunctor (second)
import Data.Primitive.Array (Array (..), indexArray, sizeofArray)
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
  => Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
caseReduce term = do
  let result = transformOf termSubterms processTerm term
  recordOptimization term CaseReduceStage result
  return result

processTerm :: CaseBuiltin uni => Term name uni fun a -> Term name uni fun a
processTerm = \case
  -- We could've rewritten those patterns as 'Error' in the 'Nothing' cases, but that would turn a
  -- structural error into an operational one, which would be unfortunate, so instead we decided
  -- not to fully optimize such scripts, since they aren't valid anyway.
  Case ann (Constr _ i args) cs
    | i < fromIntegral (sizeofArray cs) ->
        mkIterApp (indexArray cs $ fromIntegral i) ((ann,) <$> args)
  Case ann (Constant _ con) (Array cs)
    | Right t <- headSpineToTerm ann (second (Constant ann) (caseBuiltin con cs)) -> t
  t -> t
