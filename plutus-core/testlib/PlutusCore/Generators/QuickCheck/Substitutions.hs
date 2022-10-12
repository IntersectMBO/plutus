-- editorconfig-checker-disable-file

module PlutusCore.Generators.QuickCheck.Substitutions where

import Control.Monad.Except

import Control.Monad.Reader
import Control.Monad.State.Strict
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

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Subst

import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenerateTypes
import PlutusCore.Generators.QuickCheck.ShrinkTypes
import PlutusCore.Generators.QuickCheck.Utils

type TypeSub = Map TyName (Type TyName DefaultUni ())

unificationFailure :: (MonadError String m, Pretty a, Pretty b) => a -> b -> m any
unificationFailure x y = throwError $ concat
    [ "Failed to unify\n\n  "
    , display x
    , "\n\nand\n\n  "
    , display y
    , "\n\n"
    ]

resolutionFailure :: MonadError String m => TyName -> Type TyName DefaultUni () -> String -> m any
resolutionFailure name1 ty2 reason = throwError $ concat
    [ "Unification failure: cannot resolve '"
    , display name1
    , " as\n\n  "
    , display ty2
    , "\n\n because "
    , reason
    ]

{- Note [The unification algorithm]
Type unification expects a context (mapping from type variables to their kinds) and a set of
flexible type variables, also called metas (those that can get resolved). The context is used for
kind checking solutions as well as generation of fresh variables.

Internally type unification maintains a set of locals ('TyLam'- or 'TyForall'-bound variables
encountered during unification). Those are stored in a reader monad, since they depend on the
current scope and need to be adjusted when the scope changes, which is best modelled by a reader
monad.

Type unification also maintains a substitution (mapping from a possibly empty subset of metas to
their instantiations) and eventually that substitution is returned as a result of unification. The
substitution is passed around in a state monad, since unification results in one part of the
unification problem are relevant in all the other parts too (this is not in conflict with locals
being scope-specific, because flexible variable resolution cannot capture a locally bound
variable). Type unification could take a substitution as an input an extend it instead of always
making the initial substitution empty, but we didn't need this extra functionality, so we didn't
implement it for the sake of keeping the interface to the unifier simpler.

Type unification proceeds by recursion on the spines of the two types. We don't attempt to do
higher-order unification at all, so we don't have the usual unification business like pruning,
blocking, pattern unification etc. In particular, in our setting two type applications can unify
only if the functions and the arguments unify separately (with higher-order unification it would be
possible to unify type applications whose function parts differ, because functions compute and the
results may unify even if the functions don't).

We handle 'TyIFix' and 'TyFun' the same way as type applications by decomposing them into their
constituents and unifying them separately. These two would look the same in a higher-order setting.

'TyLam' and 'TyForall' being binders require a bit of special care: we rename the bound variables in
the bodies of the binders, so that the two sides of the unification equation bind the same variable,
see Note [Renaming during unification]. We do not attempt to perform unification modulo eta.

Two 'TyBuiltin's unify when they are the same built-in type.

The only remaining case is when one of the sides is a type variable (or both). There's a number of
checks that we perform in order to ensure that it's fine to resolve the variable as the given type,
those are documented alongside the code performing the checks.
-}

{- Note [Renaming during unification]
When we go under twin binders, we rename the variables that the binders introduce, so that they have
the same name. This requires travering both the sides of the unification problem before unification
can proceed. This is inefficient, instead we could do the same thing that we do for checking
equality and keep two separate maps tracking renamings of local variables. Although the types AST is
lazy, so maybe it's not a big deal in the end. Although even with laziness, we still have quadratic
behavior currently.

Note that generating a new name is also a rather expensive operation requiring to traverse the whole
context, so that's another source of inefficiency.
-}

-- See Note [The unification algorithm].
-- | Perform unification. Sound but not complete.
unifyType :: TypeCtx
          -- ^ Type context
          -> Set TyName
          -- ^ @flex@, the flexible variables (those that can be unified)
          -> Type TyName DefaultUni ()
          -- ^ @t1@
          -> Type TyName DefaultUni ()
          -- ^ @t2@
          -> Either String TypeSub
          -- ^ Either an error or a substitution (from a subset of @flex@) unifying @t1@ and @t2@
unifyType ctx flex a0 b0 =
    execStateT (runReaderT (goType (normalizeTy a0) (normalizeTy b0)) Set.empty) Map.empty
  where
    goTyName :: TyName
             -> Type TyName DefaultUni ()
             -> ReaderT (Set TyName) (StateT TypeSub (Either String)) ()
    goTyName name1 ty2 =
      -- If the variable is unified with itself, we don't need to do anything.
      when (TyVar () name1 /= ty2) $ do
        locals <- ask
        sub <- get
        case Map.lookup name1 sub of
          -- If the meta is already resolved, then look it up in the substitution and continue
          -- unification.
          Just ty1' -> goType ty1' ty2
          Nothing   -> do
            -- When a meta gets resolved, we do no substitute for all the variables in the solution,
            -- i.e. the solution can contain variables that themselves are resolved metas. Hence for
            -- computing the free variables of a type we have to look in the substitution to find
            -- the free variables of already resolved metas in there.
            -- See the definition of 'fvTypeR'.
            let fvs = fvTypeR sub ty2
            -- Cannot resolve a non-flexible type variable.
            when (not $ Set.member name1 flex) $
              resolutionFailure name1 ty2 "the variable is not meta"
            -- Cannot resolve a locally bound type variable.
            -- Covers situations like @(\x -> x) =?= (\x -> integer)@.
            when (Set.member name1 locals) $
              resolutionFailure name1 ty2 "the variable is bound"
            -- Occurs check. Covers situations like @_x =?= _x -> integer@.
            -- Note that our occurs check is pretty naive, e.g. we could've solved @_x =?= _f _x@ as
            -- @[_f := \x -> x]@ or @[_f := \_ -> _x]@, but we don't attempt to cover the
            -- higher-order case.
            when (Set.member name1 fvs) $
              resolutionFailure name1 ty2 "the variable appears free in the type"
            -- Cannot resolve a meta to an ill-kinded type.
            case checkKind ctx ty2 (Map.findWithDefault (error "impossible") name1 ctx ) of
                Left msg -> resolutionFailure name1 ty2 $ "of kind mismatch:\n\n" ++ msg
                Right () -> pure ()
            -- Cannot capture a locally bound variable.
            -- Covers situations like @(\x -> _y) =?= (\x -> x)@.
            -- As naive as the occurs check.
            when (not . null $ Set.intersection fvs locals) $
              resolutionFailure name1 ty2 $
                "the type contains bound variables: " ++ display (Set.toList locals)
            put $ Map.insert name1 ty2 sub

    goType :: Type TyName DefaultUni ()
           -> Type TyName DefaultUni ()
           -> ReaderT (Set TyName) (StateT TypeSub (Either String)) ()
    goType (TyVar _ x)         b                   = goTyName x b
    goType a                   (TyVar _ y)         = goTyName y a
    goType (TyFun _ a1 a2)     (TyFun _ b1 b2)     = goType a1 b1 *> goType a2 b2
    -- This is only structural recursion, because we don't attempt to do higher-order unification.
    goType (TyApp _ a1 a2)     (TyApp _ b1 b2)     = goType a1 b1 *> goType a2 b2
    goType (TyBuiltin _ c1)    (TyBuiltin _ c2)    = when (c1 /= c2) $ unificationFailure c1 c2
    goType (TyIFix _ a1 a2)    (TyIFix _ b1 b2)    = goType a1 b1 *> goType a2 b2
    goType (TyForall _ x k a') (TyForall _ y l b') = do
      when (k /= l) $ unificationFailure k l
      locals <- ask
      -- See Note [Renaming during unification].
      let z = freshenTyName (locals <> Map.keysSet ctx) x
      local (Set.insert z) $ goType (renameVar x z a') (renameVar y z b')
    goType (TyLam _ x k a')    (TyLam _ y l b')    = do
      when (k /= l) $ unificationFailure k l
      locals <- ask
      -- See Note [Renaming during unification].
      let z = freshenTyName (locals <> Map.keysSet ctx) x
      local (Set.insert z) $ goType (renameVar x z a') (renameVar y z b')
    goType a b = unificationFailure a b

-- CODE REVIEW: does this exist anywhere?
renameVar :: TyName -> TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
renameVar x y
    | x == y    = id
    | otherwise = substType $ Map.singleton x (TyVar () y)

-- | The most general substitution worker.
substTypeCustomGo
    :: HasCallStack
    => Bool                       -- ^ Nested ('True') or parallel ('False')
    -> Set TyName                 -- ^ Variables that are considered free.
    -> TypeSub                    -- ^ Type substitution to use.
    -> Type TyName DefaultUni ()  -- ^ Type to substitute in.
    -> Type TyName DefaultUni ()
substTypeCustomGo nested fvs0 = go fvs0 Set.empty where
    go fvs seen sub ty = case ty of
        TyVar _ x | Set.member x seen -> error "substType' loop"
        -- In the case where we do nested substitution we just continue, in parallel substitution
        -- we never go below a substitution.
        TyVar _ x | nested    -> maybe ty (go fvs (Set.insert x seen) sub) $ Map.lookup x sub
                  | otherwise -> maybe ty id $ Map.lookup x sub
        TyFun _ a b -> TyFun () (go fvs seen sub a) (go fvs seen sub b)
        TyApp _ a b -> TyApp () (go fvs seen sub a) (go fvs seen sub b)
        TyLam _ x k b
          | Set.member x fvs ->
              TyLam () x' k $ go (Set.insert x' fvs) seen sub (renameVar x x' b)
          | otherwise ->
              TyLam () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
          where x' = freshenTyName (fvs <> setOf ftvTy b) x
        TyForall _ x k b
          | Set.member x fvs ->
              TyForall () x' k $ go (Set.insert x' fvs) seen sub (renameVar x x' b)
          | otherwise ->
              TyForall () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
          where x' = freshenTyName (fvs <> setOf ftvTy b) x
        TyBuiltin{} -> ty
        TyIFix _ a b -> TyIFix () (go fvs seen sub a) (go fvs seen sub b)

-- CODE REVIEW: this function is a bit strange and I don't like it. Ideas welcome for how to
-- do this better. It basically deals with the fact that we want to be careful when substituting
-- the datatypes that escape from a term into the type. It's yucky but it works.
--
-- This might not be a welcome opinion, but working with this stuff exposes some of
-- the shortcomings of the current PIR design. It would be cleaner if a PIR program was a list
-- of declarations and datatype declarations weren't in terms.
substEscape :: Set TyName
            -> TypeSub
            -> Type TyName DefaultUni ()
            -> Type TyName DefaultUni ()
substEscape = substTypeCustomGo True

-- | Generalized substitution algorithm
substTypeCustom
    :: HasCallStack
    => Bool
    -- ^ Nested (True) or parallel (False)
    -> TypeSub
    -> Type TyName DefaultUni ()
    -> Type TyName DefaultUni ()
substTypeCustom nested sub0 ty0 = substTypeCustomGo nested fvs0 sub0 ty0 where
    fvs0 = Set.unions $ Map.keysSet sub0 : map (setOf ftvTy) (Map.elems sub0)

-- | Regular (i.e. nested type substitution).
substType
    :: HasCallStack
    => TypeSub
    -> Type TyName DefaultUni ()
    -> Type TyName DefaultUni ()
substType = substTypeCustom True

-- | Parallel substitution
substTypeParallel
    :: TypeSub
    -> Type TyName DefaultUni ()
    -> Type TyName DefaultUni ()
substTypeParallel = substTypeCustom False

-- | Find all free type variables of type `a` given substitution `sub`. If variable `x` is
-- free in `a` but in the domain of `sub` we look up `x` in `sub` and get all the free type
-- variables of the result - up to the substitution.
fvTypeR :: TypeSub -> Type TyName DefaultUni () -> Set TyName
fvTypeR sub = go where
    go = foldMap (\v -> maybe (Set.singleton v) go $ Map.lookup v sub) . setOf ftvTy

-- * Generators for substitutions

-- | Get the free type variables in a type along with how many
-- times they occur. The elements of the map are guaranteed to be
-- non-zero.
fvTypeBag :: Type TyName DefaultUni () -> Map TyName Int
fvTypeBag = toMap . multiSetOf ftvTy

-- | Generate a type substitution mapping some of the variables in the given context to some
-- arbitrary types (valid in the context).
genSubst :: TypeCtx -> Gen TypeSub
genSubst ctx0 = do
  xks <- sublistOf <=< shuffle $ Map.toList ctx0
  go ctx0 Map.empty Map.empty xks
  where
    -- Counts is used to balance the ratio between the number of times a variable @x@ occurs in the
    -- substitution and the size of the type it maps to - the more times @x@ occurs the smaller the
    -- type it maps to needs to be to avoid blowup.
    go _   sub _      []            = pure sub
    go ctx sub counts ((x, k) : xs) = do
      let
          -- @x@ is taken out from the context, because we're going to map it to a type valid in the
          -- context without @x@.
          ctx' = Map.delete x ctx
          -- How many times @x@ occurs in all the so far generated types (the ones that are in the
          -- codomain of @sub@).
          w = fromMaybe 1 $ Map.lookup x counts
      ty <- sized $ \ n -> resize (n `div` w) $ genTypeWithCtx ctx' k
      let -- Scale occurrences of all free variables of @ty@ according to how many times @x@
          -- (the variables that is being substituted for) occurs in the so far generated
          -- substitution.
          moreCounts = fmap (* w) $ fvTypeBag ty
          sub'       = Map.insert x ty sub
          counts'    = Map.unionWith (+) counts moreCounts
      go ctx' sub' counts' xs

shrinkSubst :: TypeCtx -> TypeSub -> [TypeSub]
shrinkSubst ctx0 = map Map.fromList . liftShrink shrinkTy . Map.toList
  where
    shrinkTy (x, ty) = (,) x <$> shrinkTypeAtKind (pruneCtx ctx0 ty) k ty
      where k = fromMaybe (error $ "internal error: " ++ show x ++ " not found") $ Map.lookup x ctx0
    pruneCtx ctx ty = ctx `Map.restrictKeys` setOf ftvTy ty
