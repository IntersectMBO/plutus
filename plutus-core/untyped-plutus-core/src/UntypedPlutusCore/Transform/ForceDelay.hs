{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.ForceDelay
    ( forceDelayCancel
    ) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)

forceDelayCancel :: Term name uni fun a -> Term name uni fun a
forceDelayCancel = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Force _ (Delay _ t) -> t
    t                   -> t
