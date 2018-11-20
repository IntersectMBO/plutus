-- | Normalization of PLC entities.

module Language.PlutusCore.Normalize
    ( normalizeType
    , substituteNormalizeType
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
newtype TypeEnv tyname = TypeEnv
    { unTypeEnv :: IntMap (NormalizedType tyname ())
    }

type NormalizeTypeM tyname = ReaderT (TypeEnv tyname) Quote

-- | Run a 'NormalizeTypeM' computation.
runNormalizeTypeM :: MonadQuote m => NormalizeTypeM tyname a -> m a
runNormalizeTypeM a = liftQuote $ runReaderT a (TypeEnv mempty)

-- | Locally extend a 'TypeEnv' in a 'NormalizeTypeM' computation.
withExtendedTypeEnv
    :: HasUnique (tyname ()) TypeUnique
    => tyname () -> NormalizedType tyname () -> NormalizeTypeM tyname a -> NormalizeTypeM tyname a
withExtendedTypeEnv name ty =
    local (TypeEnv . IntMap.insert (name ^. unique . coerced) ty . unTypeEnv)

-- | Look up a @tyname@ in a 'TypeEnv'.
lookupTyName
    :: HasUnique (tyname ()) TypeUnique
    => tyname () -> NormalizeTypeM tyname (Maybe (NormalizedType tyname ()))
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
    :: HasUnique (tyname ()) TypeUnique
    => Type tyname () -> NormalizeTypeM tyname (NormalizedType tyname ())
normalizeTypeM (TyForall ann name kind body) = TyForall ann name kind <<$>> normalizeTypeM body
normalizeTypeM (TyFix ann name pat)          = TyFix ann name <<$>> normalizeTypeM pat
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
    :: HasUnique (tyname ()) TypeUnique
    => NormalizedType tyname ()                          -- ^ @ty@
    -> tyname ()                                         -- ^ @name@
    -> Type tyname ()                                    -- ^ @body@
    -> NormalizeTypeM tyname (NormalizedType tyname ())  -- ^ @NORM ([ty / name] body)@
substituteNormalizeTypeM ty name = withExtendedTypeEnv name ty . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique (tyname ()) TypeUnique, MonadQuote m)
    => Type tyname () -> m (NormalizedType tyname ())
normalizeType = runNormalizeTypeM . normalizeTypeM

-- See Note [Normalizing substitution].
-- | Substitute a type for a variable in a type and normalize.
substituteNormalizeType
    :: (HasUnique (tyname ()) TypeUnique, MonadQuote m)
    => NormalizedType tyname ()      -- ^ @ty@
    -> tyname ()                     -- ^ @name@
    -> Type tyname ()                -- ^ @body@
    -> m (NormalizedType tyname ())  -- ^ @NORM ([ty / name] body)@
substituteNormalizeType ty name = runNormalizeTypeM . substituteNormalizeTypeM ty name
