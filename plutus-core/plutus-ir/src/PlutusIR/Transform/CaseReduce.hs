{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module PlutusIR.Transform.CaseReduce
    ( caseReduce
    , caseReducePass
    ) where

import PlutusCore.MkPlc
import PlutusIR.Core

import Control.Lens (transformOf, (^?))
import Data.List.Extras
import PlutusCore qualified as PLC
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

caseReducePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
caseReducePass tcconfig = simplePass "case reduce" tcconfig caseReduce

caseReduce :: Term tyname name uni fun a -> Term tyname name uni fun a
caseReduce = transformOf termSubterms processTerm

processTerm :: Term tyname name uni fun a -> Term tyname name uni fun a
processTerm = \case
    Case ann _ (Constr _ _ i args) cs | Just c <- cs ^? wix i -> mkIterApp c ((ann,) <$> args)
    t                                                         -> t
