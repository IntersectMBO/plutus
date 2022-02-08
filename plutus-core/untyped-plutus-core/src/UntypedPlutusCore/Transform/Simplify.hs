{-# LANGUAGE LambdaCase #-}
-- | Very basic simplifications on UPLC.
module UntypedPlutusCore.Transform.Simplify
    ( simplifyTerm
    ) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)

simplifyTerm :: Term name uni fun a -> Term name uni fun a
simplifyTerm = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Force _ (Delay _ t) -> t
    t                   -> t
