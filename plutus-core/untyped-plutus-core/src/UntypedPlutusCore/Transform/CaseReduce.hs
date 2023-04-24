{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.CaseReduce
    ( caseReduce
    ) where

import PlutusCore.MkPlc
import UntypedPlutusCore.Core

import Control.Lens (transformOf, (^?))
import Data.List.Extras

caseReduce :: Term name uni fun a -> Term name uni fun a
caseReduce = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Case ann (Constr _ i args) cs | Just c <- cs ^? wix i -> mkIterApp ann c args
    t                                                     -> t
