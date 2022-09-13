-- editorconfig-checker-disable-file

module PlutusCore.Generators.PIR.Substitutions where

import Control.Monad.Except

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens
import GHC.Stack
import Test.QuickCheck hiding (reason)

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Subst

import PlutusCore.Generators.PIR.Common
import PlutusCore.Generators.PIR.GenerateTypes
import PlutusCore.Generators.PIR.ShrinkTypes
import PlutusCore.Generators.PIR.Utils

{- Note [Renaming during unification]
When we go under twin binders, we rename the variables that the binders introduce, so that they have
the same name. This requires travering both the sides of the unification problem before unification
can proceed. This is inefficient, instead we could do the same thing that we do for checking
equality and keep two separate maps tracking renamings of local variables. Although the types AST is
lazy, so maybe it's not a big deal in the end. Although even with laziness, we still have quadratic
behavior currently.
-}

unificationFailure :: (Pretty a, Pretty b) => a -> b -> Either String any
unificationFailure x y = Left $ concat
    [ "Failed to unify\n\n  "
    , display x
    , "\n\nand\n\n  "
    , display y
    , "\n\n"
    ]

resolutionFailure :: TyName -> Type TyName DefaultUni () -> String -> Either String any
resolutionFailure name1 ty2 reason = Left $ concat
    [ "Unification failure: cannot resolve '"
    , display name1
    , " as\n\n  "
    , display ty2
    , "\n\n because "
    , reason
    ]

-- | Perform unification. Sound but not complete.
unifyType :: Map TyName (Kind ())
          -- ^ Type context
          -> Set TyName
          -- ^ @flex@, the flexible variables (those that can be unified)
          -> Map TyName (Type TyName DefaultUni ())
          -- ^ Existing substitution (usually empty)
          -> Type TyName DefaultUni ()
          -- ^ @t1@
          -> Type TyName DefaultUni ()
          -- ^ @t2@
          -> Either String (Map TyName (Type TyName DefaultUni ()))
          -- ^ Either an error or a substitution (from a subset of @flex@) unifying @t1@ and @t2@
unifyType ctx flex sub0 a0 b0 = goType sub0 Set.empty (normalizeTy a0) (normalizeTy b0)
  where
    goTyName sub locals name1 ty2 = case Map.lookup name1 sub of
      Just ty1' -> goType sub locals ty1' ty2
      Nothing   -> case ty2 of
        TyVar _ name2 | name1 == name2 -> pure sub
        _                              -> Map.insert name1 ty2 sub <$ do
          let fvs = fvTypeR sub ty2
          when (not $ Set.member name1 flex) $
            resolutionFailure name1 ty2 "the variable is not meta"
          -- Covers situations like @(\x -> x) =?= (\x -> integer)@.
          when (Set.member name1 locals) $
            resolutionFailure name1 ty2 "the variable is bound"
          -- Covers situations like @_x =?= _x -> integer@.
          -- Note that our occurs check is pretty naive, e.g. we could've solved @_x =?= _f _x@ as
          -- @[_f := \x -> x]@ or @[_f := \_ -> _x]@.
          when (Set.member name1 fvs) $
            resolutionFailure name1 ty2 "the variable appears free in the type"
          case checkKind ctx ty2 (ctx Map.! name1) of
              Left msg -> resolutionFailure name1 ty2 $ "of kind mismatch:\n\n" ++ msg
              Right () -> Right ()
          -- Covers situations like @(\x -> _y) =?= (\x -> x)@.
          -- As naive as the occurs check.
          when (not . null $ Set.intersection fvs locals) $
            resolutionFailure name1 ty2 $
              "the type contains bound variables: " ++ display (Set.toList locals)

    goType sub locals a b =
      case (a, b) of
        (TyVar _ x    , _)               -> goTyName sub locals x b
        (_            , TyVar _ y)       -> goTyName sub locals y a
        (TyFun _ a1 a2, TyFun _ b1 b2)   -> unifies sub locals [(a1, b1), (a2, b2)]
        (TyApp _ a1 a2, TyApp _ b1 b2)   -> unifies sub locals [(a1, b1), (a2, b2)]
        (TyBuiltin _ c1, TyBuiltin _ c2) -> sub <$ when (c1 /= c2) (unificationFailure c1 c2)
        (TyForall _ x k a', TyForall _ y k' b') | k == k' ->
          let z = freshenTyName (locals <> Map.keysSet ctx) x in
            goType sub (Set.insert z locals) (renameType x z a') (renameType y z b')
        (TyLam _ x k a', TyLam _ y k' b') | k == k' ->
          let z = freshenTyName (locals <> Map.keysSet ctx) x in
            -- See Note [Renaming during unification].
            goType sub (Set.insert z locals) (renameType x z a') (renameType y z b')
        (TyIFix _ a1 a2, TyIFix _ b1 b2) -> unifies sub locals [(a1, b1), (a2, b2)]
        _ -> unificationFailure a b

    unifies sub _ [] = pure sub
    unifies sub locals ((a, b) : tys) = do
      sub1 <- goType sub locals a b
      unifies sub1 locals tys

-- | Parallel substitution
parSubstType :: Map TyName (Type TyName DefaultUni ())
             -> Type TyName DefaultUni ()
             -> Type TyName DefaultUni ()
parSubstType = substType' False

-- CODE REVIEW: this function is a bit strange and I don't like it. Ideas welcome for how to
-- do this better. It basically deals with the fact that we want to be careful when substituting
-- the datatypes that escape from a term into the type. It's yucky but it works.
--
-- This might not be a welcome opinion, but working with this stuff exposes some of
-- the shortcomings of the current PIR design. It would be cleaner if a PIR program was a list
-- of declarations and datatype declarations weren't in terms.
-- TODO: Is this actually doing anything other than what we already do in other substitution functions?!
substEscape :: Set TyName
            -> Map TyName (Type TyName DefaultUni ())
            -> Type TyName DefaultUni ()
            -> Type TyName DefaultUni ()
substEscape fv sub ty = case ty of
  TyVar _ x        -> maybe ty (substEscape fv sub) (Map.lookup x sub)
  TyFun _ a b      -> TyFun () (substEscape fv sub a) (substEscape fv sub b)
  TyApp _ a b      -> TyApp () (substEscape fv sub a) (substEscape fv sub b)
  TyLam _ x k b    -> TyLam () x k $ substEscape (Set.insert x fv) sub b
  TyForall _ x k b -> TyForall () x k $ substEscape (Set.insert x fv) sub b
  TyBuiltin{}      -> ty
  TyIFix _ a b     -> TyIFix () (substEscape fv sub a) (substEscape fv sub b)

-- CODE REVIEW: does this exist anywhere?
renameType :: TyName -> TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
renameType x y | x == y    = id
               | otherwise = substType (Map.singleton x (TyVar () y))

substType :: HasCallStack
          => Map TyName (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Type TyName DefaultUni ()
substType = substType' True

-- | Generalized substitution algorithm
substType' :: HasCallStack
           => Bool
           -- ^ Nested (True) or parallel (False)
           -> Map TyName (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Type TyName DefaultUni ()
substType' nested sub0 ty0 = go fvs0 Set.empty sub0 ty0
  where
    fvs0 = Set.unions $ Map.keysSet sub0 : map (setOf ftvTy) (Map.elems sub0)

    go :: HasCallStack
       => Set TyName
       -> Set TyName
       -> Map TyName (Type TyName DefaultUni ())
       -> Type TyName DefaultUni ()
       -> Type TyName DefaultUni ()
    go fvs seen sub ty = case ty of
      TyVar _ x | Set.member x seen -> error "substType' loop"
      -- In the case where we do nested substitution we just continue, in parallel substitution
      -- we never go below a substitution.
      TyVar _ x | nested    -> maybe ty (go fvs (Set.insert x seen) sub) $ Map.lookup x sub
                | otherwise -> maybe ty id $ Map.lookup x sub
      TyFun _ a b      -> TyFun () (go fvs seen sub a) (go fvs seen sub b)
      TyApp _ a b      -> TyApp () (go fvs seen sub a) (go fvs seen sub b)
      TyLam _ x k b
        | Set.member x fvs -> TyLam () x' k $ go (Set.insert x' fvs) seen sub (renameType x x' b)
        | otherwise        -> TyLam () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where x' = freshenTyName (fvs <> setOf ftvTy b) x
      TyForall _ x k b
        | Set.member x fvs -> TyForall () x' k $ go (Set.insert x' fvs) seen sub (renameType x x' b)
        | otherwise        -> TyForall () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where x' = freshenTyName (fvs <> setOf ftvTy b) x
      TyBuiltin{}      -> ty
      TyIFix _ a b     -> TyIFix () (go fvs seen sub a) (go fvs seen sub b)

-- | Find all free type variables of type `a` given substitution `sub`. If variable `x` is
-- free in `a` but in the domain of `sub` we look up `x` in `sub` and get all the free type
-- variables of the result - up to the substitution.
fvTypeR :: Map TyName (Type TyName DefaultUni ()) -> Type TyName DefaultUni () -> Set TyName
fvTypeR sub a = Set.unions $ freeAndNotInSub : map (fvTypeR sub . (Map.!) sub) (Set.toList freeButInSub)
      where
          fvs = setOf ftvTy a
          subDom = Map.keysSet sub
          freeButInSub = Set.intersection subDom fvs
          freeAndNotInSub = Set.difference fvs subDom

-- * Generators for substitutions

-- | Generate a type substitution that is valid in a given context.
genSubst :: Map TyName (Kind ()) -> Gen (Map TyName (Type TyName DefaultUni ()))
genSubst ctx0 = do
  xks <- sublistOf <=< shuffle $ Map.toList ctx0
  go ctx0 Map.empty xks
  where
    -- Counts is used to balance the ratio between the number
    -- of times a variable `x` appears in the substitution and
    -- the size of the type it maps to - the more times `x` appears
    -- the smaller the type it maps to needs to be to avoid blowup.
    go _ _ [] = return mempty
    go ctx counts ((x, k) : xs) = do
      let ctx' = Map.delete x ctx
          w    = fromMaybe 1 $ Map.lookup x counts
      ty <- sized $ \ n -> resize (div n w) $ genTypeWithCtx ctx' k
      let moreCounts = fmap (* w) $ fvTypeBag ty
          counts'    = Map.unionWith (+) counts moreCounts
      Map.insert x ty <$> go ctx' counts' xs


shrinkSubst :: Map TyName (Kind ())
            -> Map TyName (Type TyName DefaultUni ())
            -> [Map TyName (Type TyName DefaultUni ())]
shrinkSubst ctx0 = map Map.fromList . liftShrink shrinkTy . Map.toList
  where
    shrinkTy (x, ty) = (,) x <$> shrinkTypeAtKind (pruneCtx ctx0 ty) k ty
      where k = fromMaybe (error $ "internal error: " ++ show x ++ " not found") $ Map.lookup x ctx0
    pruneCtx ctx ty = Map.filterWithKey (\ x _ -> Set.member x fvs) ctx
      where fvs = setOf ftvTy ty
