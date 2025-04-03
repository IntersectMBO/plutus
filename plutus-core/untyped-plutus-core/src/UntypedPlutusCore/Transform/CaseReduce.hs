{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
module UntypedPlutusCore.Transform.CaseReduce
    ( caseReduce
    ) where

import PlutusCore.MkPlc
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseReduce), SimplifierT,
                                               recordSimplification)

import Control.Lens (ix, transformOf, (^?))
import Data.Foldable (toList)

caseReduce
    :: Monad m
    => Term name uni fun a
    -> SimplifierT name uni fun a m (Term name uni fun a)
caseReduce term = do
    let result = transformOf termSubterms processTerm term
    recordSimplification term CaseReduce result
    return result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Case ann (Constr _ i args) cs | Just c <- toList cs ^? ix (fromIntegral i) ->
                                    mkIterApp c ((ann,) <$> args)
    t                                                     -> t
