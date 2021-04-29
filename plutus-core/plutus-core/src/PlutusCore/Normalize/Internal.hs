-- | The internals of the normalizer.

{-# LANGUAGE PolyKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusCore.Normalize.Internal
    ( NormalizeTypeT
    , runNormalizeTypeM
    , withExtendedTypeVarEnv
    , normalizeTypeM
    , substNormalizeTypeM
    , normalizeTypesInM
    ) where

import           PlutusCore.Core
import           PlutusCore.MkPlc     (mkTyBuiltinOf)
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Rename
import           PlutusCore.Universe
import           PlutusPrelude

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State

{- Note [Global uniqueness]
WARNING: everything in this module works under the assumption that the global uniqueness condition
is satisfied. The invariant is not checked, enforced or automatically fulfilled. So you must ensure
that the global uniqueness condition is satisfied before calling ANY function from this module.

The invariant is preserved. In future we will enforce the invariant.
-}

-- | Mapping from variables to what they stand for (each row represents a substitution).
-- Needed for efficiency reasons, otherwise we could just use substitutions.
type TypeVarEnv tyname uni ann = UniqueMap TypeUnique (Dupable (Normalized (Type tyname uni ann)))

-- | The environments that type normalization runs in.
newtype NormalizeTypeEnv tyname uni ann = NormalizeTypeEnv
    { _normalizeTypeEnvTypeVarEnv :: TypeVarEnv tyname uni ann
    }

makeLenses ''NormalizeTypeEnv

{- Note [NormalizeTypeT]
Type normalization requires 'Quote' (because we need to be able to generate fresh names), but we
do not put 'Quote' into 'NormalizeTypeT'. The reason for this is that it makes type signatures of
various runners much nicer and also more generic. For example, we have

    runNormalizeTypeM :: MonadQuote m => NormalizeTypeT m tyname uni ann a -> m a

If 'NormalizeTypeT' contained 'Quote', it would be

    runNormalizeTypeM :: NormalizeTypeT m tyname uni ann a -> QuoteT m a

which hardcodes 'QuoteT' to be the outermost transformer.

Type normalization can run in any @m@ (as long as it's a 'MonadQuote') as witnessed by
the following type signature:

    normalizeTypeM
        :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
        => Type tyname uni ann -> NormalizeTypeT m tyname uni ann (Normalized (Type tyname uni ann))

so it's natural to have runners that do not break this genericity.
-}

{- Note [Normalization API]
Normalization is split in two parts:

1. functions returning computations that perform reductions and run in defined in this module
   monad transformers (e.g. 'NormalizeTypeT')
2. runners of those computations

The reason for splitting the API is that this way the type-theoretic notion of normalization is
separated from implementation-specific details. (This used to be more important when we had
to deal with gas, and could maybe be changed now.)
-}

-- See Note [NormalizedTypeT].
-- | The monad transformer that type normalization runs in.
newtype NormalizeTypeT m tyname uni ann a = NormalizeTypeT
    { unNormalizeTypeT :: ReaderT (NormalizeTypeEnv tyname uni ann) m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad, MonadPlus
        , MonadReader (NormalizeTypeEnv tyname uni ann), MonadState s
        , MonadQuote
        )

-- | Run a 'NormalizeTypeM' computation.
runNormalizeTypeM :: NormalizeTypeT m tyname uni ann a -> m a
runNormalizeTypeM = flip runReaderT (NormalizeTypeEnv mempty) . unNormalizeTypeT

-- | Locally extend a 'TypeVarEnv' in a 'NormalizeTypeM' computation.
withExtendedTypeVarEnv
    :: (HasUnique tyname TypeUnique, Monad m)
    => tyname
    -> Normalized (Type tyname uni ann)
    -> NormalizeTypeT m tyname uni ann a
    -> NormalizeTypeT m tyname uni ann a
withExtendedTypeVarEnv name =
    local . over normalizeTypeEnvTypeVarEnv . insertByName name . pure

-- | Look up a @tyname@ in a 'TypeVarEnv'.
lookupTyNameM
    :: (HasUnique tyname TypeUnique, Monad m)
    => tyname -> NormalizeTypeT m tyname uni ann (Maybe (Dupable (Normalized (Type tyname uni ann))))
lookupTyNameM name = asks $ lookupName name . _normalizeTypeEnvTypeVarEnv

{- Note [Normalization]
Normalization works under the assumption that variables are globally unique.
We use environments instead of substitutions as they're more efficient.

Since all names are unique and there is no need to track scopes, type normalization has only two
interesting cases: function application and a variable usage. In the function application case we
normalize a function and its argument, add the normalized argument to the environment and continue
normalization. In the variable case we look up the variable in the current environment: if it's not
found, we leave the variable untouched. If the variable is found, then what this variable stands for
was previously added to an environment (while handling the function application case), so we pick
this value and rename all bound variables in it to preserve the global uniqueness condition. It is
safe to do so, because picked values cannot contain uninstantiated variables as only normalized types
are added to environments and normalization instantiates all variables presented in an environment.

See also Note [Normalization of built-in types].
-}

{- Note [Normalization of built-in types]
Instantiating a polymorphic built-in type amounts to applying it to some arguments. However,
the notion of "applying" is ambiguous, it can mean one of these two things:

1. lifting the built-in type to 'Type' and applying that via 'TyApp'
2. applying the built-in type right inside the universe to get a monomorphized type tag
   (e.g. the default universe has 'DefaultUniApply' for that purpose)

We need both of these things. The former allows us to assign types to polymorphic built-in functions
(otherwise applying a built-in type to a type variable would be unrepresentable), the latter is
used at runtime to juggle type tags so that we can avoid @unsafeCoerce@-ing, bring instances in
scope via 'bring' etc -- for all of that we have to have fully monomorphized type tags at runtime.

So in order for type checking to work we need to normalize polymorphic built-in types. For that
we simply turn intra-universe applications into regular type applications during type normalization.
-}

-- See Note [Normalization of built-in types].
-- | Normalize a built-in type by replacing each application inside the universe with regular
-- type application.
normalizeUni :: forall k (a :: k) uni tyname. HasUniApply uni => uni (T a) -> Type tyname uni ()
normalizeUni uni =
    matchUniApply
        uni
        -- If @uni@ is not an intra-universe application, then we're done.
        (mkTyBuiltinOf () uni)
        -- If it is, then we turn that application into normal type application and recurse
        -- into both the function and its argument.
        (\uniF uniA -> TyApp () (normalizeUni uniF) $ normalizeUni uniA)

-- See Note [Normalization].
-- | Normalize a 'Type' in the 'NormalizeTypeM' monad.
normalizeTypeM
    :: (HasUnique tyname TypeUnique, MonadQuote m, HasUniApply uni)
    => Type tyname uni ann -> NormalizeTypeT m tyname uni ann (Normalized (Type tyname uni ann))
normalizeTypeM (TyForall ann name kind body) =
    TyForall ann name kind <<$>> normalizeTypeM body
normalizeTypeM (TyIFix ann pat arg)          =
    TyIFix ann <<$>> normalizeTypeM pat <<*>> normalizeTypeM arg
normalizeTypeM (TyFun ann dom cod)           =
    TyFun ann <<$>> normalizeTypeM dom <<*>> normalizeTypeM cod
normalizeTypeM (TyLam ann name kind body)    =
    TyLam ann name kind <<$>> normalizeTypeM body
normalizeTypeM (TyApp ann fun arg)           = do
    vFun <- normalizeTypeM fun
    vArg <- normalizeTypeM arg
    case unNormalized vFun of
        TyLam _ nArg _ body -> substNormalizeTypeM vArg nArg body
        _                   -> pure $ TyApp ann <$> vFun <*> vArg
normalizeTypeM var@(TyVar _ name)            = do
    mayTy <- lookupTyNameM name
    case mayTy of
        -- A variable is always normalized.
        Nothing -> pure $ Normalized var
        Just ty -> liftDupable ty
normalizeTypeM (TyBuiltin ann (SomeTypeIn uni)) =
    pure . Normalized $ ann <$ normalizeUni uni

{- Note [Normalizing substitution]
@substituteNormalize[M]@ is only ever used as normalizing substitution that receives two already
normalized types. However we do not enforce this in the type signature, because
1) it's perfectly correct for the last argument to be non-normalized
2) it would be annoying to wrap 'Type's into 'NormalizedType's
-}

-- See Note [Normalizing substitution].
-- | Substitute a type for a variable in a type and normalize in the 'NormalizeTypeM' monad.
substNormalizeTypeM
    :: (HasUnique tyname TypeUnique, MonadQuote m, HasUniApply uni)
    => Normalized (Type tyname uni ann)                                    -- ^ @ty@
    -> tyname                                                              -- ^ @name@
    -> Type tyname uni ann                                                 -- ^ @body@
    -> NormalizeTypeT m tyname uni ann (Normalized (Type tyname uni ann))  -- ^ @NORM ([ty / name] body)@
substNormalizeTypeM ty name = withExtendedTypeVarEnv name ty . normalizeTypeM

-- | Normalize every 'Type' in a 'Term'.
normalizeTypesInM
    :: (HasUnique tyname TypeUnique, MonadQuote m, HasUniApply uni)
    => Term tyname name uni fun ann -> NormalizeTypeT m tyname uni ann (Term tyname name uni fun ann)
normalizeTypesInM = transformMOf termSubterms normalizeChildTypes where
    normalizeChildTypes = termSubtypes (fmap unNormalized . normalizeTypeM)
