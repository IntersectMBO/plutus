-- editorconfig-checker-disable-file
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusIR.Transform.CaseOfCase (caseOfCase, caseOfCasePass, caseOfCasePassSC) where

import Control.Lens hiding (Strict, cons)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe
import Data.Maybe
import PlutusCore qualified as PLC
import PlutusCore.Arity
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo
  ( VarInfo (DatatypeConstructor, DatatypeMatcher)
  , VarsInfo
  , getConstructorArities
  , lookupVarInfo
  , termVarInfo
  )
import PlutusIR.Contexts
import PlutusIR.Core
import PlutusIR.MkPir
import PlutusIR.Pass
import PlutusIR.Transform.Rename ()
import PlutusIR.TypeCheck qualified as TC
import PlutusPrelude

caseOfCasePassSC
  :: forall m uni fun a
   . (PLC.Typecheckable uni fun, PLC.GEq uni, PLC.MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> BuiltinsInfo uni fun
  -> Bool
  -> a
  -> Pass m TyName Name uni fun a
caseOfCasePassSC tcconfig binfo conservative newAnn =
  renamePass <> caseOfCasePass tcconfig binfo conservative newAnn

caseOfCasePass
  :: forall m uni fun a
   . (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> BuiltinsInfo uni fun
  -> Bool
  -> a
  -> Pass m TyName Name uni fun a
caseOfCasePass tcconfig binfo conservative newAnn =
  NamedPass "case-of-case" $
    Pass
      (caseOfCase binfo conservative newAnn)
      [Typechecks tcconfig, GloballyUniqueNames]
      [ConstCondition (Typechecks tcconfig)]

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
@ -}
caseOfCase
  :: forall m tyname uni fun a
   . ( Ord fun
     , PLC.HasUnique tyname PLC.TypeUnique
     , PLC.MonadQuote m -- we need this because we do generate new names
     )
  => BuiltinsInfo uni fun
  -> Bool
  -> a
  -> Term tyname Name uni fun a
  -> m (Term tyname Name uni fun a)
-- See Note [Case-of-case and conapps]
caseOfCase binfo conservative newAnn t = do
  let vinfo = termVarInfo t
  liftQuote $ transformMOf termSubterms (processTerm binfo vinfo conservative newAnn) t

processTerm
  :: forall tyname uni fun a
   . (Ord fun, PLC.HasUnique tyname PLC.TypeUnique)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname Name uni a
  -> Bool
  -> a
  -> Term tyname Name uni fun a
  -> Quote (Term tyname Name uni fun a)
processTerm binfo vinfo conservative newAnn t
  -- We have a saturated datatype matcher application
  | Just (smcO@(SplitMatchContext _ (outerScrut, _, _) _ _), reconstructOuter, _) <- splitMatch binfo vinfo t
  , -- The scrutinee is itself an application
    Just (smcI, reconstructInner, innerBranchArities) <- splitMatch binfo vinfo outerScrut =
      do
        nt <- runMaybeT $ tryDoCaseOfCase vinfo conservative newAnn (smcO, reconstructOuter) (smcI, reconstructInner) innerBranchArities
        case nt of
          Just newTerm -> pure newTerm
          Nothing -> pure t
  | otherwise = pure t

tryDoCaseOfCase
  :: VarsInfo tyname Name uni a
  -> Bool
  -> a
  -> (SplitMatchContext tyname Name uni fun a, SplitMatchContext tyname Name uni fun a -> Term tyname Name uni fun a)
  -> (SplitMatchContext tyname Name uni fun a, SplitMatchContext tyname Name uni fun a -> Term tyname Name uni fun a)
  -> [Arity]
  -> MaybeT Quote (Term tyname Name uni fun a)
tryDoCaseOfCase
  vinfo
  conservative
  newAnn
  (SplitMatchContext outerVars (_, outerScrutTy, outerScrutAnn) (outerResTy, outerResTyAnn) outerBranches, reconstructOuter)
  -- Note: we don't use the inner result type, we're going to replace it
  (SplitMatchContext innerVars (innerScrut, innerScrutTy, innerScrutAnn) _ innerBranches, reconstructInner)
  innerBranchArities =
    do
      kName <- lift $ freshName "k_caseOfCase"
      sName <- lift $ freshName "scrutinee"
      let
        -- If a term is a constructor application, returns the name of the constructor
        conAppHead (splitApplication -> (Var _ n, _)) | Just (DatatypeConstructor {}) <- lookupVarInfo n vinfo = Just n
        conAppHead _ = Nothing
        -- Gets all the constructor application heads from inside the branches of the inner match
        innerBranchConAppHeads = mapMaybe conAppHead $ innerBranches ^.. underBranches innerBranchArities
        -- Check whether a) all the branches are conapps, and b) all the conapps are distinct.
        -- See Note [Case-of-case and conapps]
        allDistinctBranchConApps =
          let
            -- Otherwise we've lost something when we did the traversal and we don't know what's going on
            lengthsMatch = length innerBranchConAppHeads == length innerBranchArities
            distinctCons = distinct innerBranchConAppHeads
           in
            lengthsMatch && distinctCons
        -- If we're being conservative (so trying to avoid code growth), and we don't know that the inlined
        -- version will reduce, then bind the outer case to a function to avoid code growth
        bindOuterCase = conservative && not allDistinctBranchConApps

      let
        mkNewOuterMatch newScrut =
          reconstructOuter $ SplitMatchContext outerVars (newScrut, outerScrutTy, outerScrutAnn) (outerResTy, outerResTyAnn) outerBranches
        -- \(x :: scrutTy) -> case x of ...
        newOuterMatchFn = LamAbs newAnn sName (newAnn <$ outerScrutTy) $ mkNewOuterMatch (Var newAnn sName)
        -- k_caseOfCase :: scrutTy -> outerResTy = ...
        newOuterMatchFnBinding =
          TermBind newAnn Strict (VarDecl newAnn kName (TyFun newAnn (newAnn <$ outerScrutTy) outerResTy)) newOuterMatchFn
        mkNewInnerBranchBody scrut =
          if bindOuterCase
            -- k_caseOfCase scrut
            then Apply newAnn (Var newAnn kName) scrut
            -- case scrut of ...
            else mkNewOuterMatch scrut

      newInnerBranches <- MaybeT $ pure $ mapBranches mkNewInnerBranchBody innerBranches innerBranchArities

      let
        newInnerMatch =
          reconstructInner $ SplitMatchContext innerVars (innerScrut, innerScrutTy, innerScrutAnn) (outerResTy, outerResTyAnn) newInnerBranches

      pure $
        if bindOuterCase
          then mkLet newAnn NonRec [newOuterMatchFnBinding] newInnerMatch
          else newInnerMatch

{-| Apply the given function to the term "inside" the case branches in the given 'AppContext'.
Must be given an arity for each branch so it knows how many binders to go under. -}
mapBranches
  :: forall tyname name uni fun a
   . (Term tyname name uni fun a -> Term tyname name uni fun a)
  -> AppContext tyname name uni fun a
  -> [Arity]
  -> Maybe (AppContext tyname name uni fun a)
mapBranches f = go
  where
    go :: AppContext tyname name uni fun a -> [Arity] -> Maybe (AppContext tyname name uni fun a)
    go AppContextEnd [] = Just AppContextEnd
    go (TermAppContext branch ann ctx) (arity : arities) =
      -- This makes the whole thing return Nothing if the traversal has no targets, i.e. if the
      -- arity doesn't match the term we're looking at. I can't see a way to do this with a more
      -- general traversal, so there's some duplication between this and the simpler 'underBranches'.
      TermAppContext <$> failover (underBinders arity) f branch <*> pure ann <*> go ctx arities
    go _ _ = Nothing

-- | Traverses under the branches in the application context.
underBranches :: [Arity] -> Traversal' (AppContext tyname name uni fun a) (Term tyname name uni fun a)
underBranches as f = go as
  where
    go [] AppContextEnd = pure AppContextEnd
    go (arity : arities) (TermAppContext branch ann ctx) =
      TermAppContext <$> underBinders arity f branch <*> pure ann <*> go arities ctx
    go _ ctx = pure ctx

-- | Split a match, either a normal datatype match or a builtin 'match'.
splitMatch
  :: forall tyname name uni fun a
   . (Ord fun, PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname name uni a
  -> Term tyname name uni fun a
  -> Maybe (SplitMatchContext tyname name uni fun a, SplitMatchContext tyname name uni fun a -> Term tyname name uni fun a, [Arity])
splitMatch binfo vinfo t = do
  let (hd, args) = splitApplication t
  (p, arities) <- case hd of
    (Var _ matcherName) -> do
      let p = asNormalDatatypeMatch vinfo matcherName
      info <- lookupVarInfo matcherName vinfo
      constrArities <- case info of
        DatatypeMatcher parentTyName -> getConstructorArities parentTyName vinfo
        _ -> Nothing
      -- The branch arities don't include the type arguments for the constructor
      let branchArities = fmap (dropWhile ((==) TypeParam)) constrArities
      pure (p, branchArities)
    (Builtin _ matcherName) -> do
      p <- asBuiltinDatatypeMatch binfo matcherName
      branchArities <- builtinDatatypeMatchBranchArities binfo matcherName
      pure (p, branchArities)
    _ -> Nothing
  withPrism p $ \reconstruct match ->
    case match args of
      Right sm ->
        -- wrangle the reconstruction function so it also puts the head back in, for
        -- convenience of use elsewhere
        pure (sm, \sm' -> fillAppContext hd (reconstruct sm'), arities)
      Left _ -> Nothing

{- Note [Case-of-case and conapps]
Case-of-case is especially good if the bodies of the branches are all constructor applications.
Consider the following program we might typically get from Plutus Tx:

Bool_match {integer} (ifThenElse {Bool} (lessThanInteger 1 2) True False) 3 4
---> case-of-case
ifThenElse {integer} (lessThanInteger 1 2) (Bool_match {integer} True 3) (Bool_match {integer} False 4)
---> case-of-known-constructor
ifThenElse {integer} (lessThanInteger 1 2) 3

That is, this guarantees that case-of-known constructor will fire and get rid of one of the
matches entirely, which is great.

In order to be sure that it's definitely good, however, we need all of the branches to
be _distinct_ constructor applications, otherwise we can duplicate code, see
Note [Case-of-case and duplicating code].
-}

{- Note [Case-of-case and duplicating code]
Case-of-case can duplicate code.

Consider this schematic example:

case (case s of { C1 a -> x; C2 b -> y; }) of
  D1 -> w
  D2 -> z

-->

case s of
  C1 a -> case x of { D1 -> w; D2 -> z; }
  C2 b -> case y of { D1 -> w; D2 -> z; }

We duplicate the outer case (the matcher application, importantly including
the branches) for every branch of the inner case.

Any time we duplicate code we run the risk of exponential program growth,
since we might apply case-of-case inside the duplicated parts of the
program, thus leading to multiplicative growth. In particular, since we apply
case-of-case in a bottom-up fashion, we can apply it inside a subterm (creating
duplication), and then in the main term (multiplying the duplication) in a single
pass. This is not _too_ bad so long as case-of-known-constructor will clear
things up afterwards, but is something to be aware of.

If the inner branch bodies are conapps (see Note [Case-of-case and conapps]) then
that will reduce but not necessarily eliminate the duplication. Consider

case (case s of { C1 a -> True; C2 b -> True; C3 c -> False }) of
  True -> v
  False -> w

--> (case-of-case)

case s of
  C1 a -> case True of { True -> v; False -> w; }
  C2 b -> case True of { True -> v; False -> w; }
  C3 c -> case False of { True -> v; False -> w; }

--> (case-of-known-constructor)

case s of
  C1 a -> v
  C2 b -> v
  C3 c -> w

i.e. we still duplicate v! If however the conapps are all distinct constructors then
this won't happen.

We can mitigate the problem by binding the potentially-duplicated code to a variable
instead:

case (case s of { C1 a -> x; C2 b -> y; }) of
  D1 -> w
  D2 -> z

-->

let k_caseOfCase = \x -> case x of { D1 -> w; D2 -> z; }
in case s of
  C1 a -> k_caseOfCase x
  C2 b -> k_caseOfCase y

This avoids the code growth but is less good as an optimization, unless we can rely
on the inliner to see these as good inlining opportunities, which we currently can't.
-}
