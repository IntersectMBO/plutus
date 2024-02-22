{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.ForceApply
    ( forceApply
    ) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)

forceApply :: Term name uni fun a -> Term name uni fun a
forceApply = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Force _ (Apply a1 (LamAbs a2 x (Delay _ t1)) t2) ->
        Apply a1 (LamAbs a2 x t1) t2
    t                   -> t
