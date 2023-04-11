{-# LANGUAGE LambdaCase #-}
module PlutusIR.Transform.CaseReduce
    ( caseReduce
    ) where

import PlutusCore.MkPlc
import PlutusIR.Core

import Control.Lens (transformOf, (^?))
import Data.List.Extras

caseReduce :: Term tyname name uni fun a -> Term tyname name uni fun a
caseReduce = transformOf termSubterms processTerm

processTerm :: Term tyname name uni fun a -> Term tyname name uni fun a
processTerm = \case
    Case ann _ (Constr _ _ i args) cs | Just c <- cs ^? wix i -> mkIterApp ann c args
    t                                                         -> t
