-- editorconfig-checker-disable-file

module PlutusCore.Generators.QuickCheck.Substitutions where

import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenerateTypes
import PlutusCore.Generators.QuickCheck.ShrinkTypes
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusIR
import PlutusIR.Subst

import Control.Monad ((<=<))
import Data.Map.Strict (Map)
import Data.Map.Strict.Internal qualified as Map
import Data.Maybe
import Data.MultiSet (toMap)
import Data.MultiSet.Lens
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens
import GHC.Stack
import Test.QuickCheck hiding (reason)

type TypeSub = Map TyName (Type TyName DefaultUni ())

{- Note [Substitution in generators]
Generators define their own substitution algorithm. It's generally useful, however it's quite
inefficient, since calling 'renameVar' in the worker when handling bindings makes the whole
algorithm at least quadratic. Plus, it also very general, since it handles both nested and parallel
substitution.

So for now we've decided to keep it local to the generators and extract it into the main library
once there's a specific reason to do that.
-}

-- | The most general substitution worker.
substTypeCustomGo
  :: HasCallStack
  => Bool
  -- ^ Nested ('True') or parallel ('False')
  -> Set TyName
  -- ^ Variables that are considered free.
  -> TypeSub
  -- ^ Type substitution to use.
  -> Type TyName DefaultUni ()
  -- ^ Type to substitute in.
  -> Type TyName DefaultUni ()
substTypeCustomGo nested fvs0 = go fvs0 Set.empty
  where
    go fvs seen sub ty = case ty of
      TyVar _ x | Set.member x seen -> error "substType' loop"
      -- In the case where we do nested substitution we just continue, in parallel substitution
      -- we never go below a substitution.
      TyVar _ x
        | nested -> maybe ty (go fvs (Set.insert x seen) sub) $ Map.lookup x sub
        | otherwise -> maybe ty id $ Map.lookup x sub
      TyFun _ a b -> TyFun () (go fvs seen sub a) (go fvs seen sub b)
      TyApp _ a b -> TyApp () (go fvs seen sub a) (go fvs seen sub b)
      TyLam _ x k b
        | Set.member x fvs ->
            -- This 'renameVar' makes the complexity of this function at the very least quadratic.
            TyLam () x' k $ go (Set.insert x' fvs) seen sub (renameVar x x' b)
        | otherwise ->
            TyLam () x k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where
          x' = freshenTyNameWith (fvs <> setOf ftvTy b) x
      TyForall _ x k b
        | Set.member x fvs ->
            -- This 'renameVar' makes the complexity of this function at the very least quadratic.
            TyForall () x' k $ go (Set.insert x' fvs) seen sub (renameVar x x' b)
        | otherwise ->
            TyForall () x k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where
          x' = freshenTyNameWith (fvs <> setOf ftvTy b) x
      TyBuiltin {} -> ty
      TyIFix _ a b -> TyIFix () (go fvs seen sub a) (go fvs seen sub b)
      TySOP _ tyls -> TySOP () ((fmap . fmap) (go fvs seen sub) tyls)

-- CODE REVIEW: this function is a bit strange and I don't like it. Ideas welcome for how to
-- do this better. It basically deals with the fact that we want to be careful when substituting
-- the datatypes that escape from a term into the type. It's yucky but it works.
--
-- This might not be a welcome opinion, but working with this stuff exposes some of
-- the shortcomings of the current PIR design. It would be cleaner if a PIR program was a list
-- of declarations and datatype declarations weren't in terms.
substEscape
  :: Set TyName
  -> TypeSub
  -> Type TyName DefaultUni ()
  -> Type TyName DefaultUni ()
substEscape = substTypeCustomGo True

-- See Note [Substitution in generators].
-- | Generalized substitution algorithm.
substTypeCustom
  :: HasCallStack
  => Bool
  -- ^ Nested (True) or parallel (False)
  -> TypeSub
  -> Type TyName DefaultUni ()
  -> Type TyName DefaultUni ()
substTypeCustom nested sub0 ty0 = substTypeCustomGo nested fvs0 sub0 ty0
  where
    fvs0 = Set.unions $ Map.keysSet sub0 : map (setOf ftvTy) (Map.elems sub0)

-- See Note [Substitution in generators].
-- | Regular (i.e. nested type substitution).
substType
  :: HasCallStack
  => TypeSub
  -> Type TyName DefaultUni ()
  -> Type TyName DefaultUni ()
substType = substTypeCustom True

-- See Note [Substitution in generators].
-- | Parallel substitution.
substTypeParallel
  :: TypeSub
  -> Type TyName DefaultUni ()
  -> Type TyName DefaultUni ()
substTypeParallel = substTypeCustom False

-- | Rename one variable to another.
renameVar :: TyName -> TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
renameVar x y
  | x == y = id
  | otherwise = substType $ Map.singleton x (TyVar () y)

{-| Find all free type variables of type `a` given substitution `sub`. If variable `x` is
free in `a` but in the domain of `sub` we look up `x` in `sub` and get all the free type
variables of the result - up to the substitution. -}
fvTypeR :: TypeSub -> Type TyName DefaultUni () -> Set TyName
fvTypeR sub = go
  where
    go = foldMap (\v -> maybe (Set.singleton v) go $ Map.lookup v sub) . setOf ftvTy

-- * Generators for substitutions

{-| Get the free type variables in a type along with how many
times they occur. The elements of the map are guaranteed to be
non-zero. -}
fvTypeBag :: Type TyName DefaultUni () -> Map TyName Int
fvTypeBag = toMap . multiSetOf ftvTy

{-| Generate a type substitution mapping some of the variables in the given context to some
arbitrary types (valid in the context). -}
genSubst :: TypeCtx -> Gen TypeSub
genSubst ctx0 = do
  xks <- sublistOf <=< shuffle $ Map.toList ctx0
  go ctx0 Map.empty Map.empty xks
  where
    -- Counts is used to balance the ratio between the number of times a variable @x@ occurs in the
    -- substitution and the size of the type it maps to - the more times @x@ occurs the smaller the
    -- type it maps to needs to be to avoid blowup.
    go _ sub _ [] = pure sub
    go ctx sub counts ((x, k) : xs) = do
      let
        -- @x@ is taken out from the context, because we're going to map it to a type valid in the
        -- context without @x@.
        ctx' = Map.delete x ctx
        -- How many times @x@ occurs in all the so far generated types (the ones that are in the
        -- codomain of @sub@).
        w = fromMaybe 1 $ Map.lookup x counts
      ty <- sized $ \n -> resize (n `div` w) $ genTypeWithCtx ctx' k
      let
        -- Scale occurrences of all free variables of @ty@ according to how many times @x@
        -- (the variables that is being substituted for) occurs in the so far generated
        -- substitution.
        moreCounts = fmap (* w) $ fvTypeBag ty
        sub' = Map.insert x ty sub
        counts' = Map.unionWith (+) counts moreCounts
      go ctx' sub' counts' xs

shrinkSubst :: TypeCtx -> TypeSub -> [TypeSub]
shrinkSubst ctx0 = map Map.fromList . liftShrink shrinkTy . Map.toList
  where
    shrinkTy (x, ty) = (,) x <$> shrinkTypeAtKind (pruneCtx ctx0 ty) k ty
      where
        k = fromMaybe (error $ "internal error: " ++ show x ++ " not found") $ Map.lookup x ctx0
    pruneCtx ctx ty = ctx `Map.restrictKeys` setOf ftvTy ty
