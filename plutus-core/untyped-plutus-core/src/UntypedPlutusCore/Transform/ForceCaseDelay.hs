{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Transform.ForceCaseDelay
  ( forceCaseDelay,
  )
where

import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (ForceCaseDelay), SimplifierT,
                                               recordSimplification)

import Control.Lens

forceCaseDelay
    :: Monad m
    => Term name uni fun a
    -> SimplifierT name uni fun a m (Term name uni fun a)
forceCaseDelay term = do
  let result = transformOf termSubterms processTerm term
  recordSimplification term ForceCaseDelay result
  return result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
  original@(Force _ (Case cAnn scrut branches)) ->
    let mNewBranches = traverse findDelayUnderLambdas branches
     in case mNewBranches of
          Just newBranches ->
            Case cAnn scrut newBranches
          Nothing -> original
  other -> other
  where
    findDelayUnderLambdas :: Term name uni fun a -> Maybe (Term name uni fun a)
    findDelayUnderLambdas = \case
      LamAbs ann var body -> LamAbs ann var <$> findDelayUnderLambdas body
      Delay _ term    -> Just term
      _               -> Nothing
