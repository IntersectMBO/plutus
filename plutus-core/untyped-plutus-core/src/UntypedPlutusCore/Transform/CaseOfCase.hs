{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

{- |
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
-}
module UntypedPlutusCore.Transform.CaseOfCase (caseOfCase) where

import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin (CaseBuiltin (..))
import PlutusCore.MkPlc (mkIterApp)
import UntypedPlutusCore.Core
import UntypedPlutusCore.Transform.CaseReduce qualified as CaseReduce
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CaseOfCase), SimplifierT,
                                               recordSimplification)

import Control.Lens
import Data.Set qualified as Set

caseOfCase
    :: (fun ~ PLC.DefaultFun, Monad m, CaseBuiltin (Term name uni fun a) uni)
    => Term name uni fun a
    -> SimplifierT name uni fun a m (Term name uni fun a)
caseOfCase term = do
  let result = transformOf termSubterms processTerm term
  recordSimplification term CaseOfCase result
  return result

processTerm
    :: fun ~ PLC.DefaultFun
    => CaseBuiltin (Term name uni fun a) uni => Term name uni fun a -> Term name uni fun a
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
