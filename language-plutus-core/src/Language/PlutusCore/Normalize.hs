-- | Normalization of PLC entities.

module Language.PlutusCore.Normalize
    ( normalizeType
    , substituteNormalizeType
    , normalizeTypesIn
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens
import           Control.Monad.Reader
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as IntMap

-- | Type environments contain
newtype TypeEnv tyname ann = TypeEnv
    { unTypeEnv :: IntMap (NormalizedType tyname ann)
    }

type NormalizeTypeM tyname ann = ReaderT (TypeEnv tyname ann) Quote

-- | Run a 'NormalizeTypeM' computation.
runNormalizeTypeM :: MonadQuote m => NormalizeTypeM tyname ann a -> m a
runNormalizeTypeM a = liftQuote $ runReaderT a (TypeEnv mempty)

-- | Locally extend a 'TypeEnv' in a 'NormalizeTypeM' computation.
withExtendedTypeEnv
    :: HasUnique (tyname ann) TypeUnique
    => tyname ann
    -> NormalizedType tyname ann
    -> NormalizeTypeM tyname ann a
    -> NormalizeTypeM tyname ann a
withExtendedTypeEnv name ty =
    local (TypeEnv . IntMap.insert (name ^. unique . coerced) ty . unTypeEnv)

-- | Look up a @tyname@ in a 'TypeEnv'.
lookupTyName
    :: HasUnique (tyname ann) TypeUnique
    => tyname ann -> NormalizeTypeM tyname ann (Maybe (NormalizedType tyname ann))
lookupTyName name = asks $ IntMap.lookup (name ^. unique . coerced) . unTypeEnv

{- Note [Normalization]
Normalization works under the assumption that variables are globally unique.
We use environments instead of substitutions as they're more efficient.

Since all names are unique and there is no need to track scopes, type normalization has only two
interesting cases: function application and a variable usage. In the function application case we
normalize a function and its argument, add the normalized argument to the environment and continue
normalization. In the variable case we look up the variable in the current environment: if it's not
found, we leave the variable untouched. If the variable is found, then what this variable stands for
was previously added to an environment (while handling the function application case), so we pick this
value and rename all bound variables in it to preserve the global uniqueness condition. It is safe to
do so, because picked values cannot contain uninstantiated variables as only normalized types are
added to environments and normalization instantiates all variables presented in an environment.
-}

-- See Note [Normalization].
-- | Normalize a 'Type' in the 'NormalizeTypeM' monad.
normalizeTypeM
    :: HasUnique (tyname ann) TypeUnique
    => Type tyname ann -> NormalizeTypeM tyname ann (NormalizedType tyname ann)
normalizeTypeM (TyForall ann name kind body) = TyForall ann name kind <<$>> normalizeTypeM body
normalizeTypeM (TyIFix ann pat arg)           =
    TyIFix ann <<$>> normalizeTypeM pat <<*>> normalizeTypeM arg
normalizeTypeM (TyFun ann dom cod)           =
    TyFun ann <<$>> normalizeTypeM dom <<*>> normalizeTypeM cod
normalizeTypeM (TyLam ann name kind body)    = TyLam ann name kind <<$>> normalizeTypeM body
normalizeTypeM (TyApp ann fun arg)           = do
    vFun <- normalizeTypeM fun
    vArg <- normalizeTypeM arg
    case getNormalizedType vFun of
        TyLam _ nArg _ body -> substituteNormalizeTypeM vArg nArg body
        _                   -> pure $ TyApp ann <$> vFun <*> vArg
normalizeTypeM var@(TyVar _ name)            = do
    mayTy <- lookupTyName name
    case mayTy of
        Nothing -> pure $ NormalizedType var
        Just ty -> traverse rename ty
normalizeTypeM size@TyInt{}                  = pure $ NormalizedType size
normalizeTypeM builtin@TyBuiltin{}           = pure $ NormalizedType builtin

{- Note [Normalizing substitution]
@substituteNormalize[M]@ is only ever used as normalizing substitution that receives two already
normalized types. However we do not enforce this in the type signature, because
1) it's perfectly correct for the last argument to be non-normalized
2) it would be annoying to wrap 'Type's into 'NormalizedType's
-}

-- See Note [Normalizing substitution].
-- | Substitute a type for a variable in a type and normalize in the 'NormalizeTypeM' monad.
substituteNormalizeTypeM
    :: HasUnique (tyname ann) TypeUnique
    => NormalizedType tyname ann                              -- ^ @ty@
    -> tyname ann                                             -- ^ @name@
    -> Type tyname ann                                        -- ^ @body@
    -> NormalizeTypeM tyname ann (NormalizedType tyname ann)  -- ^ @NORM ([ty / name] body)@
substituteNormalizeTypeM ty name = withExtendedTypeEnv name ty . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> m (NormalizedType tyname ann)
normalizeType = runNormalizeTypeM . normalizeTypeM

-- See Note [Normalizing substitution].
-- | Substitute a type for a variable in a type and normalize.
substituteNormalizeType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => NormalizedType tyname ann      -- ^ @ty@
    -> tyname ann                     -- ^ @name@
    -> Type tyname ann                -- ^ @body@
    -> m (NormalizedType tyname ann)  -- ^ @NORM ([ty / name] body)@
substituteNormalizeType ty name = runNormalizeTypeM . substituteNormalizeTypeM ty name

normalizeReturnType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> m (Type tyname ann)
normalizeReturnType = fmap getNormalizedType . normalizeType

normalizeTypesIn
    :: HasUnique (tyname a) TypeUnique
    => Term tyname name a -> Quote (Term tyname name a)
normalizeTypesIn (LamAbs ann name ty body)  =
    LamAbs ann name <$> normalizeReturnType ty <*> normalizeTypesIn body
normalizeTypesIn (TyAbs ann name kind body) =
    TyAbs ann name kind <$> normalizeTypesIn body
normalizeTypesIn (IWrap ann pat arg term)   =
    IWrap ann <$> normalizeReturnType pat <*> normalizeReturnType arg <*> normalizeTypesIn term
normalizeTypesIn (Apply ann fun arg)        =
    Apply ann <$> normalizeTypesIn fun <*> normalizeTypesIn arg
normalizeTypesIn (Unwrap ann term)          =
    Unwrap ann <$> normalizeTypesIn term
normalizeTypesIn (Error ann ty)             =
    Error ann <$> normalizeReturnType ty
normalizeTypesIn (TyInst ann body ty)       =
    TyInst ann <$> normalizeTypesIn body <*> normalizeReturnType ty
normalizeTypesIn (Var ann name)             =
    return $ Var ann name
normalizeTypesIn con@Constant{}             =
    pure con
normalizeTypesIn bi@Builtin{}               =
    pure bi
