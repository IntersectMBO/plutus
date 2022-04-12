{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.LamDelay
    ( lamToDelay
    ) where

import PlutusCore.Core (HasUniques)
import PlutusCore.Name
import UntypedPlutusCore.Core

import Control.Lens

lamToDelay :: HasUniques (Term name uni fun ann) => Term name uni fun a -> Term name uni fun a
lamToDelay = transformOf termSubterms processTerm

processTerm :: HasUniques (Term name uni fun ann) => Term name uni fun a -> Term name uni fun a
processTerm = \case
    l@(LamAbs ann n t) ->
        let us = t^..termUniquesDeep
        in if n^.theUnique `elem` us
           then l
           else Delay ann t
    t                   -> t
