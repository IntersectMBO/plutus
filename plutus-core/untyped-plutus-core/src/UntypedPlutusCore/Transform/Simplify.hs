{-# LANGUAGE LambdaCase #-}
-- | Very basic simplifications on UPLC.
module UntypedPlutusCore.Transform.Simplify
    ( simplifyTerm
    , simplifyProgram
    ) where

import           UntypedPlutusCore.Core

import           Control.Lens           (transformOf)

simplifyProgram :: Program name uni fun a -> Program name uni fun a
simplifyProgram (Program a v t) = Program a v $ simplifyTerm t

simplifyTerm :: Term name uni fun a -> Term name uni fun a
simplifyTerm = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Force _ (Delay _ t) -> t
    t                   -> t
