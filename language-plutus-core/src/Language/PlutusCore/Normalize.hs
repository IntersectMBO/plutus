-- | Normalization of PLC entities.

-- Due to the generated 'normalizeEnvCountStep' below which is not used.
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}

module Language.PlutusCore.Normalize
    ( NormalizeTypeT
    , runNormalizeTypeM
    , runNormalizeTypeAnyM
    , runNormalizeTypeGasM
    , withExtendedTypeArgEnv
    , normalizeTypeM
    , normalizeTypeAny
    , substituteNormalizeTypeM
    , normalizeTypesIn
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.IntMap                 (IntMap)
import qualified Data.IntMap                 as IntMap

newtype TypeArgEnv tyname ann = TypeArgEnv
    { unTypeArgEnv :: IntMap (NormalizedType tyname ann)
    }

data NormalizeTypeEnv m tyname ann = NormalizeTypeEnv
    { _normalizeTypeEnvTypeArgEnv :: TypeArgEnv tyname ann
    , _normalizeTypeEnvCountStep  :: m ()
    }

makeLenses ''NormalizeTypeEnv

-- We do not have `QuoteT` here for nice constraints.
newtype NormalizeTypeT m tyname ann a = NormalizeTypeT
    { unNormalizeTypeT :: ReaderT (NormalizeTypeEnv m tyname ann) m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad, MonadPlus
        , MonadReader (NormalizeTypeEnv m tyname ann), MonadState s
        , MonadQuote
        )

type CountSubstT m = StateT Gas (MaybeT m)

type NormalizeTypeAnyM = NormalizeTypeT Quote
type NormalizeTypeGasM = NormalizeTypeT (CountSubstT Quote)

countSubst :: Monad m => CountSubstT m ()
countSubst = do
    Gas gas <- get
    if gas == 0
        then mzero
        else put . Gas $ gas - 1

-- | Run a 'NormalizeTypeM' computation.
runNormalizeTypeM :: m () -> NormalizeTypeT m tyname ann a -> m a
runNormalizeTypeM countStep (NormalizeTypeT a) =
    runReaderT a $ NormalizeTypeEnv (TypeArgEnv mempty) countStep

-- | Run a 'NormalizeTypeM' computation ignoring gas.
runNormalizeTypeAnyM :: MonadQuote m => NormalizeTypeT m tyname ann a -> m a
runNormalizeTypeAnyM = runNormalizeTypeM $ pure ()

-- | Run a 'NormalizeTypeM' computation consuming gas.
runNormalizeTypeGasM :: Gas -> NormalizeTypeT (CountSubstT Quote) tyname ann a -> Quote (Maybe a)
runNormalizeTypeGasM gas a = runMaybeT $ evalStateT (runNormalizeTypeM countSubst a) gas

-- | Locally extend a 'TypeArgEnv' in a 'NormalizeTypeM' computation.
withExtendedTypeArgEnv
    :: (HasUnique (tyname ann) TypeUnique, Monad m)
    => tyname ann
    -> NormalizedType tyname ann
    -> NormalizeTypeT m tyname ann a
    -> NormalizeTypeT m tyname ann a
withExtendedTypeArgEnv name ty =
    local . over (normalizeTypeEnvTypeArgEnv . coerced) $
        IntMap.insert (name ^. unique . coerced) ty

-- | Look up a @tyname@ in a 'TypeArgEnv'.
lookupTyName
    :: (HasUnique (tyname ann) TypeUnique, Monad m)
    => tyname ann -> NormalizeTypeT m tyname ann (Maybe (NormalizedType tyname ann))
lookupTyName name =
    asks $ IntMap.lookup (name ^. unique . coerced) . unTypeArgEnv . _normalizeTypeEnvTypeArgEnv

countTypeNormalizationStep :: NormalizeTypeT m tyname ann ()
countTypeNormalizationStep = NormalizeTypeT . ReaderT $ _normalizeTypeEnvCountStep

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
-}

-- See Note [Normalization].
-- | Normalize a 'Type' in the 'NormalizeTypeM' monad.
normalizeTypeM
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> NormalizeTypeT m tyname ann (NormalizedType tyname ann)
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
    case getNormalizedType vFun of
        TyLam _ nArg _ body -> do
            countTypeNormalizationStep
            substituteNormalizeTypeM vArg nArg body
        _                   -> pure $ TyApp ann <$> vFun <*> vArg
normalizeTypeM var@(TyVar _ name)            = do
    mayTy <- lookupTyName name
    case mayTy of
        Nothing -> pure $ NormalizedType var
        Just ty -> traverse rename ty
normalizeTypeM size@TyInt{}                  =
    pure $ NormalizedType size
normalizeTypeM builtin@TyBuiltin{}           =
    pure $ NormalizedType builtin

{- Note [Normalizing substitution]
@substituteNormalize[M]@ is only ever used as normalizing substitution that receives two already
normalized types. However we do not enforce this in the type signature, because
1) it's perfectly correct for the last argument to be non-normalized
2) it would be annoying to wrap 'Type's into 'NormalizedType's
-}

-- See Note [Normalizing substitution].
-- | Substitute a type for a variable in a type and normalize in the 'NormalizeTypeM' monad.
substituteNormalizeTypeM
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => NormalizedType tyname ann                                -- ^ @ty@
    -> tyname ann                                               -- ^ @name@
    -> Type tyname ann                                          -- ^ @body@
    -> NormalizeTypeT m tyname ann (NormalizedType tyname ann)  -- ^ @NORM ([ty / name] body)@
substituteNormalizeTypeM ty name = withExtendedTypeArgEnv name ty . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type'.
normalizeType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => m () -> Type tyname ann -> m (NormalizedType tyname ann)
normalizeType countStep = runNormalizeTypeM countStep . normalizeTypeM

-- See Note [Normalization].
-- | Normalize a 'Type' ignoring sizes.
normalizeTypeAny
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> m (NormalizedType tyname ann)
normalizeTypeAny = normalizeType $ pure ()

normalizeReturnType
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Type tyname ann -> NormalizeTypeT m tyname ann (Type tyname ann)
normalizeReturnType = fmap getNormalizedType . normalizeTypeM

normalizeTypesIn
    :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
    => Term tyname name ann -> NormalizeTypeT m tyname ann (Term tyname name ann)
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

-- -- See Note [Normalizing substitution].
-- -- | Substitute a type for a variable in a type and normalize.
-- substituteNormalizeType
--     :: (HasUnique (tyname ann) TypeUnique, MonadQuote m)
--     => m ()
--     -> NormalizedType tyname ann      -- ^ @ty@
--     -> tyname ann                     -- ^ @name@
--     -> Type tyname ann                -- ^ @body@
--     -> m (NormalizedType tyname ann)  -- ^ @NORM ([ty / name] body)@
-- substituteNormalizeType countStep ty name =
--     runNormalizeTypeM countStep . substituteNormalizeTypeM ty name
