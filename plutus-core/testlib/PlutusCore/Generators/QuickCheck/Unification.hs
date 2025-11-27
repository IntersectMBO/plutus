-- editorconfig-checker-disable-file

module PlutusCore.Generators.QuickCheck.Unification where

import PlutusPrelude

import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenerateTypes
import PlutusCore.Generators.QuickCheck.Substitutions
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusIR

import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.State.Strict (StateT, execStateT, get, put)
import Data.Map.Strict.Internal qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

unificationFailure :: (MonadError String m, Pretty a, Pretty b) => a -> b -> m any
unificationFailure x y =
  throwError $
    concat
      [ "Failed to unify\n\n  "
      , display x
      , "\n\nand\n\n  "
      , display y
      , "\n\n"
      ]

resolutionFailure :: MonadError String m => TyName -> Type TyName DefaultUni () -> String -> m any
resolutionFailure name1 ty2 reason =
  throwError $
    concat
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
variable). Type unification could take a substitution as an input and extend it instead of always
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
unifyType
  :: TypeCtx
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
    goTyName
      :: TyName
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
          Nothing -> do
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
            case checkKind ctx ty2 (Map.findWithDefault (error "impossible") name1 ctx) of
              Left msg -> resolutionFailure name1 ty2 $ "of kind mismatch:\n\n" ++ msg
              Right () -> pure ()
            -- Cannot capture a locally bound variable.
            -- Covers situations like @(\x -> _y) =?= (\x -> x)@.
            -- As naive as the occurs check.
            when (not . null $ Set.intersection fvs locals) $
              resolutionFailure name1 ty2 $
                "the type contains bound variables: " ++ display (Set.toList locals)
            put $ Map.insert name1 ty2 sub

    goType
      :: Type TyName DefaultUni ()
      -> Type TyName DefaultUni ()
      -> ReaderT (Set TyName) (StateT TypeSub (Either String)) ()
    goType (TyVar _ x) b = goTyName x b
    goType a (TyVar _ y) = goTyName y a
    goType (TyFun _ a1 a2) (TyFun _ b1 b2) = goType a1 b1 *> goType a2 b2
    -- This is only structural recursion, because we don't attempt to do higher-order unification.
    goType (TyApp _ a1 a2) (TyApp _ b1 b2) = goType a1 b1 *> goType a2 b2
    goType (TyBuiltin _ c1) (TyBuiltin _ c2) = when (c1 /= c2) $ unificationFailure c1 c2
    goType (TyIFix _ a1 a2) (TyIFix _ b1 b2) = goType a1 b1 *> goType a2 b2
    goType (TyForall _ x k a') (TyForall _ y l b') = do
      when (k /= l) $ unificationFailure k l
      locals <- ask
      -- See Note [Renaming during unification].
      let z = freshenTyNameWith (locals <> Map.keysSet ctx) x
      local (Set.insert z) $ goType (renameVar x z a') (renameVar y z b')
    goType (TyLam _ x k a') (TyLam _ y l b') = do
      when (k /= l) $ unificationFailure k l
      locals <- ask
      -- See Note [Renaming during unification].
      let z = freshenTyNameWith (locals <> Map.keysSet ctx) x
      local (Set.insert z) $ goType (renameVar x z a') (renameVar y z b')
    goType (TySOP _ sum1) (TySOP _ sum2)
      -- Sums must be of the same arity.
      | Just sum12 <- zipExact sum1 sum2 =
          for_ sum12 $ \(prod1, prod2) -> do
            -- Products within sums must be of the same arity.
            case zipExact prod1 prod2 of
              Nothing -> unificationFailure prod1 prod2
              -- SOPs unify componentwise.
              Just prod12 -> traverse_ (uncurry goType) prod12
    goType a b = unificationFailure a b
