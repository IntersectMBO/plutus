{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
module UntypedPlutusCore.Transform.CaseReduce
    ( caseReduce
    ) where

import PlutusCore.Compiler.Types
import PlutusCore.MkPlc
import UntypedPlutusCore.Core

import Control.Lens (transformOf)
import Control.Monad.State.Class (MonadState)
import Data.Vector qualified as V

caseReduce
    :: MonadState (UPLCSimplifierTrace name uni fun a) m
    => Term name uni fun a
    -> m (Term name uni fun a)
caseReduce term = do
    let result = transformOf termSubterms processTerm term
    recordSimplification term CaseReduce result
    return result

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Case ann (Constr _ i args) cs | Just c <- (V.!?) cs (fromIntegral i) ->
                                    mkIterApp c ((ann,) <$> args)
    t                                                     -> t
