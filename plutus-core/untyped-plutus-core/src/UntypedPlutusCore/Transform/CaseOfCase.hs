{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
import UntypedPlutusCore.Transform.Optimizer
  ( OptimizerT
  , recordOptimization
  , pattern CaseOfCaseStage
  )

import Control.Lens
import Data.List (nub)
import Data.Set qualified as Set
import Data.Typeable (eqT)
import Data.Vector qualified as Vector

caseOfCase
  :: forall name uni fun m a
   . ( Typeable name
     , Typeable uni
     , fun ~ PLC.DefaultFun
     , Monad m
     , CaseBuiltin uni
     , PLC.GEq uni
     , PLC.Closed uni
     , uni `PLC.Everywhere` Eq
     )
  => Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
caseOfCase term = do
  let result = case (eqT @name @PLC.Name, eqT @uni @PLC.DefaultUni) of
        (Just Refl, Just Refl) -> simplifyWithListFacts term
        _ -> transformOf termSubterms processTerm term
  recordOptimization term CaseOfCaseStage result
  return result

-- The second field supplied by a non-empty builtin list, or by the builtin pair
-- returned by unConstrData, is itself a list. Carry that fact into its branch,
-- so subsequent uncons operations on the tail can fuse in the same traversal.
simplifyWithListFacts
  :: Term PLC.Name PLC.DefaultUni PLC.DefaultFun a
  -> Term PLC.Name PLC.DefaultUni PLC.DefaultFun a
simplifyWithListFacts = go Set.empty
  where
    go lists term = processTerm $ case fuseUncons lists term of
      Case a scrut alts ->
        let goAlt 0 (LamAbs b h (LamAbs c t body))
              | knownList lists scrut || isConstrDataPair scrut =
                  LamAbs b h $ LamAbs c t $ go (Set.insert t (Set.delete h lists)) body
            goAlt _ alt = go lists alt
         in Case a (go lists scrut) (Vector.imap goAlt alts)
      Apply a (LamAbs b n body) rhs
        | knownList lists rhs ->
            Apply a (LamAbs b n (go (Set.insert n lists) body)) (go lists rhs)
      LamAbs a n body -> LamAbs a n $ go (Set.delete n lists) body
      other -> over termSubterms (go lists) other

isConstrDataPair :: Term name uni PLC.DefaultFun a -> Bool
isConstrDataPair (Apply _ (Builtin _ PLC.UnConstrData) _) = True
isConstrDataPair _ = False

-- Only the result on success matters: the new case evaluates the same scrutinee.
knownList :: Set.Set PLC.Name -> Term PLC.Name PLC.DefaultUni PLC.DefaultFun a -> Bool
knownList lists = \case
  Var _ n -> Set.member n lists
  Constant _ (PLC.Some (PLC.ValueOf (PLC.DefaultUniList _) _)) -> True
  Apply _ (Builtin _ f) _ ->
    f `elem` [PLC.UnListData, PLC.UnMapData, PLC.MkNilData, PLC.MkNilPairData]
  Apply _ (Force _ (Builtin _ PLC.TailList)) _ -> True
  Apply _ (Apply _ (Force _ (Builtin _ PLC.MkCons)) _) _ -> True
  Apply _ (Force _ (Force _ (Builtin _ PLC.SndPair))) pair -> isConstrDataPair pair
  _ -> False

-- case (case xs [\h t -> Just (h,t), Nothing]) [\p -> case p [k], n]
--   ==> case xs [k, n]
-- The list proof is essential. For example, a nullary SOP constructor with tag
-- zero would leave the original inner branch partially applied.
fuseUncons
  :: Set.Set PLC.Name
  -> Term PLC.Name PLC.DefaultUni PLC.DefaultFun a
  -> Term PLC.Name PLC.DefaultUni PLC.DefaultFun a
fuseUncons lists (Case _ (Case a xs inner) outer)
  | [consBranch, Constr _ 1 []] <- toList inner
  , LamAbs _ h (LamAbs _ t (Constr _ 0 [Constr _ 0 [Var _ x, Var _ y]])) <- consBranch
  , h == x && t == y && h /= t
  , [LamAbs _ p (Case _ (Var _ v) branches), nil] <- toList outer
  , p == v
  , [k] <- toList branches
  , knownList lists xs
  , not (occursFree p k) =
      Case a xs (Vector.fromList [k, nil])
fuseUncons _ term = term

occursFree :: Eq name => name -> Term name uni fun a -> Bool
occursFree name = \case
  Var _ v -> name == v
  LamAbs _ v _ | name == v -> False
  other -> anyOf termSubterms (occursFree name) other

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
