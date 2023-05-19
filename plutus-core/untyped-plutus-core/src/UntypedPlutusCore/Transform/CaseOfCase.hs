{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

{- | A special case of case-of-case optimisation: transforms

@
    case ((force ifThenElse) b (constr t) (constr f)) alts
@

into

@
    force ifThenElse b (case (constr t) branches) (case (constr f) branches)
@

This is always an improvement.
-}
module UntypedPlutusCore.Transform.CaseOfCase (caseOfCase) where

import PlutusCore qualified as PLC
import UntypedPlutusCore.Core

import Control.Lens

caseOfCase :: (fun ~ PLC.DefaultFun) => Term name uni fun a -> Term name uni fun a
caseOfCase = transformOf termSubterms $ \case
  Case ann scrut alts
    | ( ite@(Force _ (Builtin _ PLC.IfThenElse))
        , [cond, (true@Constr{}, trueAnn), (false@Constr{}, falseAnn)]
        ) <-
        splitApplication scrut ->
        mkApplication ite [cond, (Case ann true alts, trueAnn), (Case ann false alts, falseAnn)]
  other -> other
