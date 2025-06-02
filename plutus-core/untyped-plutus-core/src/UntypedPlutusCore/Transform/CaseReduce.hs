{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
module UntypedPlutusCore.Transform.CaseReduce
    ( caseReduce
    , processTerm
    ) where

import PlutusCore.Builtin (CaseBuiltin (..))
import PlutusCore.MkPlc
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseReduce), SimplifierT,
                                               recordSimplification)

import Control.Lens (transformOf)
import Data.Vector qualified as V

caseReduce
    :: (Monad m, CaseBuiltin uni)
    => Term name uni fun a
    -> SimplifierT name uni fun a m (Term name uni fun a)
caseReduce term = do
    let result = transformOf termSubterms processTerm term
    recordSimplification term CaseReduce result
    return result

processTerm :: CaseBuiltin uni => Term name uni fun a -> Term name uni fun a
processTerm = \case
    Case ann (Constr _ i args) cs | Just c <- (V.!?) cs (fromIntegral i) ->
                                    mkIterApp c ((ann,) <$> args)
    Case ann (Constant _ con) cs -> case caseBuiltin con cs of
        Left _    -> Error ann
        Right res -> res
    t -> t
