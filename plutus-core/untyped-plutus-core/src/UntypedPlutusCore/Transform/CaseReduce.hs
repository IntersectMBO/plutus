{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
module UntypedPlutusCore.Transform.CaseReduce
    ( caseReduce
    ) where

import PlutusCore.MkPlc
import UntypedPlutusCore.Core

import Control.Lens (transformOf)
import Data.Vector qualified as V

caseReduce :: Term name uni fun a -> Term name uni fun a
caseReduce = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Case ann (Constr _ i args) cs | Just c <- (V.!?) cs (fromIntegral i) ->
        mkIterApp c ((ann,) <$> args)
    t                                                     -> t
