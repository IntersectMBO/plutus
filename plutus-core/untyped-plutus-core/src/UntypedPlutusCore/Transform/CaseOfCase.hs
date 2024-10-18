{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

{- | A special case of case-of-case optimisation: transforms

@
    case ((force ifThenElse) b (constr t) (constr f)) alts
@

into

@
    force ifThenElse b (delay (case (constr t) alts)) (delay (case (constr f) alts))
@

This is always an improvement.
-}
module UntypedPlutusCore.Transform.CaseOfCase (caseOfCase) where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseOfCase), SimplifierT,
                                               recordSimplification)

import Control.Lens

caseOfCase
    :: fun ~ PLC.DefaultFun
    => Monad m
    => Term name uni fun a
    -> SimplifierT name uni fun a m (Term name uni fun a)
caseOfCase term = do
  let result = transformOf termSubterms processTerm term
  recordSimplification term CaseOfCase result
  return result

processTerm :: (fun ~ PLC.DefaultFun) => Term name uni fun a -> Term name uni fun a
processTerm = \case
  Case ann scrut alts
    | ( ite@(Force a (Builtin _ PLC.IfThenElse))
        , [cond, (trueAnn, true@Constr{}), (falseAnn, false@Constr{})]
        ) <-
        splitApplication scrut ->
        Force a $
          mkIterApp
            ite
            [ cond
            , (trueAnn, Delay trueAnn (Case ann true alts))
            , (falseAnn, Delay falseAnn (Case ann false alts))
            ]
  other -> other
