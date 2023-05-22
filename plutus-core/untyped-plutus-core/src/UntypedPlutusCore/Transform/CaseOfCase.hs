{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

{- | A special case of case-of-case optimisation: transforms

@
    case ((force ifThenElse) b (constr t) (constr f)) alts
@

into

@
    force ifThenElse b (case (constr t) alts) (case (constr f) alts)
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
        , [cond, Arg trueAnn true@Constr{}, Arg falseAnn false@Constr{}]
        ) <-
        splitApplication scrut ->
        mkApplication
          ite
          [cond, Arg trueAnn (Case ann true alts), Arg falseAnn (Case ann false alts)]
  other -> other
