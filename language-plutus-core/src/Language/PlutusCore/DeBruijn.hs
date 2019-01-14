{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module Language.PlutusCore.DeBruijn (
                                Ix (..)
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

import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

import           Control.Exception
import           Control.Lens               hiding (Level, index, ix)
import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.Bimap                 as BM
import qualified Data.Text                  as T
import           Data.Typeable

import           Numeric.Natural

import           GHC.Generics

-- | A relative index used for de Bruijn identifiers.
newtype Ix = Ix Natural
    deriving stock Generic
    deriving newtype (Show, Num, Eq, Ord)

-- | A term name as a de Bruijn index.
data DeBruijn a = DeBruijn { dbnAttribute :: a, dbnString :: T.Text, dbnIndex :: Ix }
    deriving (Show, Functor, Generic)

-- | A type name as a de Bruijn index.
newtype TyDeBruijn a = TyDeBruijn (DeBruijn a)
    deriving (Show, Functor, Generic)
instance Wrapped (TyDeBruijn a)

instance HasPrettyConfigName config => PrettyBy config (DeBruijn a) where
    prettyBy config (DeBruijn _ txt (Ix ix))
        | showsUnique = pretty txt <> "_i" <> pretty ix
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique _ = toPrettyConfigName config

deriving newtype instance HasPrettyConfigName config => PrettyBy config (TyDeBruijn a)

class HasIx a where
    index :: Lens' a Ix

instance HasIx (DeBruijn a) where
    index = lens g s where
        g = dbnIndex
        s n i = n{dbnIndex=i}

instance HasIx (TyDeBruijn a) where
    index = _Wrapped' . index

-- Converting from normal names to DeBruijn indices, and vice versa

{- Note [Levels and indices]
The indices that we use for de Bruijn identifiers are *relative*. However,
when doing conversions it is easier to work with *absolute* levels, since  that
way we don't have to adjust them all when we go under a binder.

However, this means that we *do* need to adjust them when we use them or record them.
The adjustment is fairly straightforward:
- An index `i` points to a binder `i` levels above (smaller than) the current level, so the level
  of `i` is `current - i`.
- A level `l` which is `i` levels above (smaller than) the current level has an index of `i`, so it
  is also calculated as `current - l`.

We use a newtype to keep these separate, since getting it wrong will leads to annoying bugs.
-}

-- | An absolute level in the program.
newtype Level = Level Ix deriving newtype (Eq, Ord, Num)
data Levels = Levels Level (BM.Bimap Unique Level)

-- | Compute the absolute 'Level' of a relative 'Ix' relative to the current 'Level'.
ixToLevel :: Level -> Ix -> Level
ixToLevel (Level current) ix = Level (current - ix)

-- | Compute the relative 'Ix' of a absolute 'Level' relative to the current 'Level'.
levelToIx :: Level -> Level -> Ix
levelToIx (Level current) (Level l) = current - l

-- | Declare a name with a unique, recording the mapping to a 'Level'.
declareUnique :: (MonadReader Levels m, HasUnique name unique) => name -> m a -> m a
declareUnique n = local $ \(Levels current ls) -> Levels current $ BM.insert (n ^. unique . coerced) current ls

-- | Declare a name with an index, recording the mapping from the corresponding 'Level' to a fresh unique.
declareIx :: (MonadReader Levels m, MonadQuote m, HasIx name) => name -> m a -> m a
declareIx n act = do
    newU <- freshUnique
    local (\(Levels current ls) -> Levels current $ BM.insert newU (ixToLevel current (n ^. index)) ls) act

-- | Enter a scope, incrementing the current 'Level' by one
withScope :: (MonadReader Levels m) => m a -> m a
withScope = local $ \(Levels current ls) -> Levels (current+1) ls

-- | We cannot do a correct translation to or from de Bruijn indices if the program is not well-scoped.
-- So we throw an error in such a case.
data FreeVariableError = FreeUnique Unique | FreeIndex Ix deriving (Show, Typeable, Eq, Ord)
instance Exception FreeVariableError

-- | Get the 'Ix' corresponding to a given 'Unique'.
getIndex :: (MonadReader Levels m, MonadError FreeVariableError m) => Unique -> m Ix
getIndex u = do
    Levels current ls <- ask
    case BM.lookup u ls of
        Just ix -> pure $ levelToIx current ix
        Nothing -> throwError $ FreeUnique u

-- | Get the 'Unique' corresponding to a given 'Ix'.
getUnique :: (MonadReader Levels m, MonadError FreeVariableError m) => Ix -> m Unique
getUnique ix = do
    Levels current ls <- ask
    case BM.lookupR (ixToLevel current ix) ls of
        Just u  -> pure u
        Nothing -> throwError $ FreeIndex ix

nameToDeBruijn :: (MonadReader Levels m, MonadError FreeVariableError m) => Name a -> m (DeBruijn a)
nameToDeBruijn (Name x str u) = DeBruijn x str <$> getIndex u

tyNameToDeBruijn :: (MonadReader Levels m, MonadError FreeVariableError m) => TyName a -> m (TyDeBruijn a)
tyNameToDeBruijn (TyName n) = TyDeBruijn <$> nameToDeBruijn n

deBruijnToName :: (MonadReader Levels m, MonadError FreeVariableError m) => DeBruijn a -> m (Name a)
deBruijnToName (DeBruijn x str ix) = Name x str <$> getUnique ix

deBruijnToTyName :: (MonadReader Levels m, MonadError FreeVariableError m) => TyDeBruijn a -> m (TyName a)
deBruijnToTyName (TyDeBruijn n) = TyName <$> deBruijnToName n

-- | Convert a 'Type' with 'TyName's into a 'Type' with 'TyDeBruijn's.
deBruijnTy :: (MonadError FreeVariableError m) => Type TyName a -> m (Type TyDeBruijn a)
deBruijnTy = flip runReaderT (Levels 0 BM.empty) . deBruijnTyM

-- | Convert a 'Term' with 'TyName's and 'Name's into a 'Term' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnTerm :: (MonadError FreeVariableError m) => Term TyName Name a -> m (Term TyDeBruijn DeBruijn a)
deBruijnTerm = flip runReaderT (Levels 0 BM.empty) . deBruijnTermM

-- | Convert a 'Program' with 'TyName's and 'Name's into a 'Program' with 'TyDeBruijn's and 'DeBruijn's.
deBruijnProgram :: (MonadError FreeVariableError m) => Program TyName Name a -> m (Program TyDeBruijn DeBruijn a)
deBruijnProgram (Program x v t) = Program x v <$> deBruijnTerm t

{- Note [De Bruijn conversion and recursion schemes]
These are quite repetitive, but we can't use a catamorphism for this, because
we are not only altering the recursive type, but also the name type parameters.
These are normally constant in a catamorphic application.
-}
deBruijnTyM
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Type TyName a
    -> m (Type TyDeBruijn a)
deBruijnTyM = \case
    -- variable case
    TyVar x n -> TyVar x <$> tyNameToDeBruijn n
    -- binder cases
    TyForall x tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyForall x tn' k <$> deBruijnTyM ty
    TyLam x tn k ty -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyLam x tn' k <$> deBruijnTyM ty
    -- boring recursive cases
    TyFun x i o -> TyFun x <$> deBruijnTyM i <*> deBruijnTyM o
    TyApp x fun arg -> TyApp x <$> deBruijnTyM fun <*> deBruijnTyM arg
    TyIFix x pat arg -> TyIFix x <$> deBruijnTyM pat <*> deBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin x bn -> pure $ TyBuiltin x bn
    TyInt x nat -> pure $ TyInt x nat

deBruijnTermM
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Term TyName Name a
    -> m (Term TyDeBruijn DeBruijn a)
deBruijnTermM = \case
    -- variable case
    Var x n -> Var x <$> nameToDeBruijn n
    -- binder cases
    TyAbs x tn k t -> declareUnique tn $ do
        tn' <- tyNameToDeBruijn tn
        withScope $ TyAbs x tn' k <$> deBruijnTermM t
    LamAbs x n ty t -> declareUnique n $ do
        n' <- nameToDeBruijn n
        withScope $ LamAbs x n' <$> deBruijnTyM ty <*> deBruijnTermM t
    -- boring recursive cases
    Apply x t1 t2 -> Apply x <$> deBruijnTermM t1 <*> deBruijnTermM t2
    TyInst x t ty -> TyInst x <$> deBruijnTermM t <*> deBruijnTyM ty
    Unwrap x t -> Unwrap x <$> deBruijnTermM t
    IWrap x pat arg t -> IWrap x <$> deBruijnTyM pat <*> deBruijnTyM arg <*> deBruijnTermM t
    Error x ty -> Error x <$> deBruijnTyM ty
    -- boring non-recursive cases
    Constant x con -> pure $ Constant x con
    Builtin x bn -> pure $ Builtin x bn

-- | Convert a 'Type' with 'TyDeBruijn's into a 'Type' with 'TyName's.
unDeBruijnTy :: (MonadQuote m, MonadError FreeVariableError m) => Type TyDeBruijn a -> m (Type TyName a)
unDeBruijnTy = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTyM

-- | Convert a 'Term' with 'TyDeBruijn's and 'DeBruijn's into a 'Term' with 'TyName's and 'Name's.
unDeBruijnTerm :: (MonadQuote m, MonadError FreeVariableError m) => Term TyDeBruijn DeBruijn a -> m (Term TyName Name a)
unDeBruijnTerm = flip runReaderT (Levels 0 BM.empty) . unDeBruijnTermM

-- | Convert a 'Program' with 'TyDeBruijn's and 'DeBruijn's into a 'Program' with 'TyName's and 'Name's.
unDeBruijnProgram :: (MonadQuote m, MonadError FreeVariableError m) => Program TyDeBruijn DeBruijn a -> m (Program TyName Name a)
unDeBruijnProgram (Program x v t) = Program x v <$> unDeBruijnTerm t

unDeBruijnTyM
    :: (MonadReader Levels m, MonadQuote m, MonadError FreeVariableError m)
    => Type TyDeBruijn a
    -> m (Type TyName a)
unDeBruijnTyM = \case
    -- variable case
    TyVar x n -> TyVar x <$> deBruijnToTyName n
    -- binder cases
    TyForall x tn k ty -> declareIx tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyForall x tn' k <$> unDeBruijnTyM ty
    TyLam x tn k ty -> declareIx tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyLam x tn' k <$> unDeBruijnTyM ty
    -- boring recursive cases
    TyFun x i o -> TyFun x <$> unDeBruijnTyM i <*> unDeBruijnTyM o
    TyApp x fun arg -> TyApp x <$> unDeBruijnTyM fun <*> unDeBruijnTyM arg
    TyIFix x pat arg -> TyIFix x <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg
    -- boring non-recursive cases
    TyBuiltin x bn -> pure $ TyBuiltin x bn
    TyInt x nat -> pure $ TyInt x nat

unDeBruijnTermM
    :: (MonadReader Levels m, MonadQuote m, MonadError FreeVariableError m)
    => Term TyDeBruijn DeBruijn a
    -> m (Term TyName Name a)
unDeBruijnTermM = \case
    -- variable case
    Var x n -> Var x <$> deBruijnToName n
    -- binder cases
    TyAbs x tn k t -> declareIx tn $ do
        tn' <- deBruijnToTyName tn
        withScope $ TyAbs x tn' k <$> unDeBruijnTermM t
    LamAbs x n ty t -> declareIx n $ do
        n' <- deBruijnToName n
        withScope $ LamAbs x n' <$> unDeBruijnTyM ty <*> unDeBruijnTermM t
    -- boring recursive cases
    Apply x t1 t2 -> Apply x <$> unDeBruijnTermM t1 <*> unDeBruijnTermM t2
    TyInst x t ty -> TyInst x <$> unDeBruijnTermM t <*> unDeBruijnTyM ty
    Unwrap x t -> Unwrap x <$> unDeBruijnTermM t
    IWrap x pat arg t -> IWrap x <$> unDeBruijnTyM pat <*> unDeBruijnTyM arg <*> unDeBruijnTermM t
    Error x ty -> Error x <$> unDeBruijnTyM ty
    -- boring non-recursive cases
    Constant x con -> pure $ Constant x con
    Builtin x bn -> pure $ Builtin x bn
