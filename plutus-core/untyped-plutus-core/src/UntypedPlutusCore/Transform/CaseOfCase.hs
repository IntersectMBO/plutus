{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Perform the case-of-case transformation. This pushes
case expressions into the case branches of other case
expressions, which can often yield optimization opportunities.

Example:
@
    case (case s of { C1 a -> x; C2 b -> y; }) of
      D1 -> w
      D2 -> z

    -->

    case s of
      C1 a -> case x of { D1 -> w; D2 -> z; }
      C2 b -> case y of { D1 -> w; D2 -> z; }
@

We also transform

@
    case ((force ifThenElse) b (constr t) (constr f)) alts
@

into

@
    force (force ifThenElse b (delay (case (constr t) alts)) (delay (case (constr f) alts)))
@

This is always an improvement. -}
module UntypedPlutusCore.Transform.CaseOfCase (caseOfCase) where

import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin (CaseBuiltin (..))
import PlutusCore.MkPlc (mkIterApp)
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.CaseReduce qualified as CaseReduce
import UntypedPlutusCore.Transform.Simplifier
  ( SimplifierStage (CaseOfCase)
  , SimplifierT
  , recordSimplification
  )

import Control.Lens
import Data.List (nub)

caseOfCase
  :: ( fun ~ PLC.DefaultFun
     , Monad m
     , CaseBuiltin uni
     , PLC.GEq uni
     , PLC.Closed uni
     , uni `PLC.Everywhere` Eq
     )
  => Term name uni fun a
  -> SimplifierT name uni fun a m (Term name uni fun a)
caseOfCase term = do
  let result = transformOf termSubterms processTerm term
  recordSimplification term CaseOfCase result
  return result

processTerm
  :: ( fun ~ PLC.DefaultFun
     , CaseBuiltin uni
     , PLC.GEq uni
     , PLC.Closed uni
     , uni `PLC.Everywhere` Eq
     )
  => Term name uni fun a -> Term name uni fun a
processTerm = \case
  Case ann scrut alts
    | ( ite@(Force a (Builtin _ PLC.IfThenElse))
        , [cond, (trueAnn, true@Constr {}), (falseAnn, false@Constr {})]
        ) <-
        splitApplication scrut ->
        Force a $
          mkIterApp
            ite
            [ cond
            , -- Here we call a single step of case-reduce in order to immediately clean up the
              -- duplication of @alts@. Otherwise optimizing case-of-case-of-case-of... would create
              -- exponential blowup of the case branches, which would eventually get deduplicated
              -- with case-reduce, but only after that exponential blowup has already slowed the
              -- optimizer down unnecessarily.
              (trueAnn, Delay trueAnn . CaseReduce.processTerm $ Case ann true alts)
            , (falseAnn, Delay falseAnn . CaseReduce.processTerm $ Case ann false alts)
            ]
  original@(Case annOuter (Case annInner scrut altsInner) altsOuter) ->
    maybe
      original
      (Case annInner scrut)
      ( do
          constrs <- for altsInner $ \case
            c@(Constr _ i _) -> Just (Left i, c)
            c@(Constant _ val) -> Just (Right val, c)
            _ -> Nothing
          -- See Note [Case-of-case and duplicating code].
          guard $ length (nub . toList $ fmap fst constrs) == length constrs
          pure $ constrs <&> \(_, c) -> CaseReduce.processTerm $ Case annOuter c altsOuter
      )
  other -> other
