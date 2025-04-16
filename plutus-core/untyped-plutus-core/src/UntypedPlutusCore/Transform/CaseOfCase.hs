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

import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.MkPlc
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.CaseReduce qualified as CaseReduce
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseOfCase), SimplifierT,
                                               recordSimplification)

import Control.Lens
import Data.Set qualified as Set

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
  original@(Case annOuter (Case annInner scrut altsInner) altsOuter) ->
    maybe
      original
      (Case annInner scrut)
      (do
        constrs <- for altsInner $ \case
          c@(Constr _ i _) -> Just (i, c)
          _                -> Nothing
        -- See Note [Case-of-case and duplicating code].
        guard $ length (Set.fromList . toList $ fmap fst constrs) == length constrs
        pure $ constrs <&> \(_, c) -> CaseReduce.processTerm $ Case annOuter c altsOuter)
  other -> other
