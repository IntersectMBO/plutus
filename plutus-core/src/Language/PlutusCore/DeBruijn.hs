{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module Language.PlutusCore.DeBruijn
    ( Index (..)
    , DeBruijn (..)
    , TyDeBruijn (..)
    , FreeVariableError (..)
    , deBruijnTy
    , deBruijnTerm
    , deBruijnProgram
    , unDeBruijnTy
    , unDeBruijnTerm
    , unDeBruijnProgram
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote

import           Control.Exception
import           Control.Lens               hiding (Index, Level, index, ix)
import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Bimap                 as BM
import qualified Data.Text                  as T
import           Data.Typeable

import           Numeric.Natural

import           GHC.Generics

-- | A relative index used for de Bruijn identifiers.
newtype Index = Index Natural
    deriving stock Generic
    deriving newtype (Show, Num, Eq, Ord)

-- | A term name as a de Bruijn index.
data DeBruijn = DeBruijn { dbnString :: T.Text, dbnIndex :: Index }
    deriving (Show, Generic)

-- | A type name as a de Bruijn index.
newtype TyDeBruijn = TyDeBruijn DeBruijn
    deriving (Show, Generic, PrettyBy config)
instance Wrapped TyDeBruijn

instance HasPrettyConfigName config => PrettyBy config DeBruijn where
    prettyBy config (DeBruijn txt (Index ix))
        | showsUnique = pretty txt <> "_i" <> pretty ix
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique = toPrettyConfigName config

class HasIndex a where
    index :: Lens' a Index

instance HasIndex DeBruijn where
    index = lens g s where
        g = dbnIndex
        s n i = n{dbnIndex=i}

instance HasIndex TyDeBruijn where
    index = _Wrapped' . index

-- Converting from normal names to DeBruijn indices, and vice versa

{- Note [Levels and indices]
The indices ('Index') that we actually store as our de Bruijn indices in the program
are *relative* - that is, they say how many levels above the *current* level to look for
the binder.

However, when doing conversions it is easier to record the  *absolute* level of a variable,
in our state, since that way we don't have to adjust our mapping when we go under a binder (whereas
for relative indices we would need to increment them all by one, as the current level has increased).

However, this means that we *do* need to do an adjustment when we store an index as a level or extract
a level to use it as an index. The adjustment is fairly straightforward:
- An index `i` points to a binder `i` levels above (smaller than) the current level, so the level
  of `i` is `current - i`.
- A level `l` which is `i` levels above (smaller than) the current level has an index of `i`, so it
  is also calculated as `current - l`.

We use a newtype to keep these separate, since getting it wrong will leads to annoying bugs.
-}

-- | An absolute level in the program.
newtype Level = Level Index deriving newtype (Eq, Ord, Num)
data Levels = Levels Level (BM.Bimap Unique Level)

-- | Compute the absolute 'Level' of a relative 'Index' relative to the current 'Level'.
ixToLevel :: Level -> Index -> Level
ixToLevel (Level current) ix = Level (current - ix)

-- | Compute the relative 'Index' of a absolute 'Level' relative to the current 'Level'.
levelToIndex :: Level -> Level -> Index
levelToIndex (Level current) (Level l) = current - l

-- | Declare a name with a unique, recording the mapping to a 'Level'.
declareUnique :: (MonadReader Levels m, HasUnique name unique) => name -> m a -> m a
declareUnique n =
    local $ \(Levels current ls) -> Levels current $ BM.insert (n ^. theUnique) current ls

-- | Declare a name with an index, recording the mapping from the corresponding 'Level' to a fresh unique.
declareIndex :: (MonadReader Levels m, MonadQuote m, HasIndex name) => name -> m a -> m a
declareIndex n act = do
    newU <- freshUnique
    local (\(Levels current ls) -> Levels current $ BM.insert newU (ixToLevel current (n ^. index)) ls) act

-- | Enter a scope, incrementing the current 'Level' by one
withScope :: MonadReader Levels m => m a -> m a
withScope = local $ \(Levels current ls) -> Levels (current+1) ls

-- | We cannot do a correct translation to or from de Bruijn indices if the program is not well-scoped.
-- So we throw an error in such a case.
data FreeVariableError
    = FreeUnique Unique
    | FreeIndex Index
    deriving (Show, Typeable, Eq, Ord)
instance Exception FreeVariableError

-- | Get the 'Index' corresponding to a given 'Unique'.
getIndex :: (MonadReader Levels m, MonadError FreeVariableError m) => Unique -> m Index
getIndex u = do
    Levels current ls <- ask
    case BM.lookup u ls of
        Just ix -> pure $ levelToIndex current ix
        Nothing -> throwError $ FreeUnique u

-- | Get the 'Unique' corresponding to a given 'Index'.
getUnique :: (MonadReader Levels m, MonadError FreeVariableError m) => Index -> m Unique
getUnique ix = do
    Levels current ls <- ask
    case BM.lookupR (ixToLevel current ix) ls of
        Just u  -> pure u
        Nothing -> throwError $ FreeIndex ix

nameToDeBruijn
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Name -> m DeBruijn
nameToDeBruijn (Name str u) = DeBruijn str <$> getIndex u

tyNameToDeBruijn
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => TyName -> m TyDeBruijn
tyNameToDeBruijn (TyName n) = TyDeBruijn <$> nameToDeBruijn n

deBruijnToName
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => DeBruijn -> m Name
deBruijnToName (DeBruijn str ix) = Name str <$> getUnique ix

deBruijnToTyName
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => TyDeBruijn -> m TyName
deBruijnToTyName (TyDeBruijn n) = TyName <$> deBruijnToName n

-- | Convert a 'Type' with 'TyName's into a 'Type' with 'TyDeBruijn's.
deBruijnTy
    :: MonadError FreeVariableError m
    => Type TyName uni ann -> m (Type TyDeBruijn uni ann)
deBruijnTy = flip runReaderT (Levels 0 BM.empty) . deBruijnTyM

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnTerm
    :: MonadError FreeVariableError m
    => Term TyName Name uni ann -> m (Term TyDeBruijn DeBruijn uni ann)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with 'TyName's and 'Name's into a 'Program' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnProgram
    :: MonadError FreeVariableError m
    => Program TyName Name uni ann -> m (Program TyDeBruijn DeBruijn uni ann)
deBruijnProgram (Program ann ver term) = Program ann ver <$> deBruijnTerm term

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}
deBruijnTyM
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Type TyName uni ann
    -> m (Type TyDeBruijn uni ann)
deBruijnTyM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> tyNameToDeBruijn n
    -- binder cases
    TyForall ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyForall ann tn' k <$> deBruijnTyM ty
    TyLam ann tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyLam ann tn' k <$> deBruijnTyM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> deBruijnTyM i <*> deBruijnTyM o
    TyApp ann fun arg -> TyApp ann <$> deBruijnTyM fun <*> deBruijnTyM arg
    TyIFix ann pat arg -> TyIFix ann <$> deBruijnTyM pat <*> deBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

deBruijnTermM
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Term TyName Name uni ann
    -> m (Term TyDeBruijn DeBruijn uni ann)
deBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> nameToDeBruijn n
    -- binder cases
    TyAbs ann tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyAbs ann tn' k <$> deBruijnTermM t
    LamAbs ann n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs ann n' <$> deBruijnTyM ty <*> deBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> deBruijnTermM t1 <*> deBruijnTermM t2
    TyInst ann t ty -> TyInst ann <$> deBruijnTermM t <*> deBruijnTyM ty
    Unwrap ann t -> Unwrap ann <$> deBruijnTermM t
    IWrap ann pat arg t -> IWrap ann <$> deBruijnTyM pat <*> deBruijnTyM arg <*> deBruijnTermM t
    Error ann ty -> Error ann <$> deBruijnTyM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn

-- | Convert a 'Type' with 'TyDeBruijn's into a 'Type' with 'TyName's.
unDeBruijnTy
    :: (MonadQuote m, MonadError FreeVariableError m)
    => Type TyDeBruijn uni ann -> m (Type TyName uni ann)
unDeBruijnTy = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTyM

-- | Convert a 'Term' with 'TyDeBruijn's and 'DeBruijn's into a 'Term' with 'TyName's and 'Name's.
unDeBruijnTerm
    :: (MonadQuote m, MonadError FreeVariableError m)
    => Term TyDeBruijn DeBruijn uni ann -> m (Term TyName Name uni ann)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'TyDeBruijn's and 'DeBruijn's into a 'Program' with 'TyName's and 'Name's.
unDeBruijnProgram
    :: (MonadQuote m, MonadError FreeVariableError m)
    => Program TyDeBruijn DeBruijn uni ann -> m (Program TyName Name uni ann)
unDeBruijnProgram (Program ann ver term) = Program ann ver <$> unDeBruijnTerm term

unDeBruijnTyM
    :: (MonadReader Levels m, MonadQuote m, MonadError FreeVariableError m)
    => Type TyDeBruijn uni ann
    -> m (Type TyName uni ann)
unDeBruijnTyM = \case
    -- variable case
    TyVar ann n -> TyVar ann <$> deBruijnToTyName n
    -- binder cases
    TyForall ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyForall ann tn' k <$> unDeBruijnTyM ty
    TyLam ann tn k ty -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyLam ann tn' k <$> unDeBruijnTyM ty
    -- boring recursive cases
    TyFun ann i o -> TyFun ann <$> unDeBruijnTyM i <*> unDeBruijnTyM o
    TyApp ann fun arg -> TyApp ann <$> unDeBruijnTyM fun <*> unDeBruijnTyM arg
    TyIFix ann pat arg -> TyIFix ann <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin ann con -> pure $ TyBuiltin ann con

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, MonadError FreeVariableError m)
    => Term TyDeBruijn DeBruijn uni ann
    -> m (Term TyName Name uni ann)
unDeBruijnTermM = \case
    -- variable case
    Var ann n -> Var ann <$> deBruijnToName n
    -- binder cases
    TyAbs ann tn k t -> declareIndex tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyAbs ann tn' k <$> unDeBruijnTermM t
    LamAbs ann n ty t -> declareIndex n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs ann n' <$> unDeBruijnTyM ty <*> unDeBruijnTermM t
    -- boring recursive cases
    Apply ann t1 t2 -> Apply ann <$> unDeBruijnTermM t1 <*> unDeBruijnTermM t2
    TyInst ann t ty -> TyInst ann <$> unDeBruijnTermM t <*> unDeBruijnTyM ty
    Unwrap ann t -> Unwrap ann <$> unDeBruijnTermM t
    IWrap ann pat arg t -> IWrap ann <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg <*> unDeBruijnTermM t
    Error ann ty -> Error ann <$> unDeBruijnTyM ty
    -- boring non-recursive cases
    Constant ann con -> pure $ Constant ann con
    Builtin ann bn -> pure $ Builtin ann bn
