{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Support for using de Bruijn indices for term and type names.
module Language.PlutusCore.DeBruijn.Internal
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , TyDeBruijn (..)
    , NamedTyDeBruijn (..)
    , FreeVariableError (..)
    , Level (..)
    , Levels (..)
    , ixToLevel
    , levelToIndex
    , declareUnique
    , declareIndex
    , withScope
    , getIndex
    , getUnique
    , unNameDeBruijn
    , unNameTyDeBruijn
    , nameToDeBruijn
    , tyNameToDeBruijn
    , deBruijnToName
    , deBruijnToTyName
    ) where

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

import           Control.DeepSeq            (NFData)
import           GHC.Generics

-- | A relative index used for de Bruijn identifiers.
newtype Index = Index Natural
    deriving stock Generic
    deriving newtype (Show, Num, Eq, Ord)
    deriving anyclass NFData

-- | A term name as a de Bruijn index.
data NamedDeBruijn = NamedDeBruijn { ndbnString :: T.Text, ndbnIndex :: Index }
    deriving (Show, Generic)
    deriving anyclass NFData

-- | A term name as a de Bruijn index, without the name string.
data DeBruijn = DeBruijn { dbnIndex :: Index }
    deriving (Show, Generic)
    deriving anyclass NFData

-- | A type name as a de Bruijn index.
newtype NamedTyDeBruijn = NamedTyDeBruijn NamedDeBruijn
    deriving stock (Show, Generic)
    deriving newtype (PrettyBy config)
    deriving anyclass NFData
instance Wrapped NamedTyDeBruijn

-- | A type name as a de Bruijn index, without the name string.
newtype TyDeBruijn = TyDeBruijn DeBruijn
    deriving stock (Show, Generic)
    deriving newtype (PrettyBy config)
    deriving anyclass NFData
instance Wrapped TyDeBruijn

instance HasPrettyConfigName config => PrettyBy config NamedDeBruijn where
    prettyBy config (NamedDeBruijn txt (Index ix))
        | showsUnique = pretty txt <> "_i" <> pretty ix
        | otherwise   = pretty txt
        where PrettyConfigName showsUnique = toPrettyConfigName config

instance HasPrettyConfigName config => PrettyBy config DeBruijn where
    prettyBy config (DeBruijn (Index ix))
        | showsUnique = "i" <> pretty ix
        | otherwise   = ""
        where PrettyConfigName showsUnique = toPrettyConfigName config

class HasIndex a where
    index :: Lens' a Index

instance HasIndex NamedDeBruijn where
    index = lens g s where
        g = ndbnIndex
        s n i = n{ndbnIndex=i}

instance HasIndex DeBruijn where
    index = lens g s where
        g = dbnIndex
        s n i = n{dbnIndex=i}

instance HasIndex NamedTyDeBruijn where
    index = _Wrapped' . index

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

We use a newtype to keep these separate, since getting it wrong will lead to annoying bugs.
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

unNameDeBruijn
    :: NamedDeBruijn -> DeBruijn
unNameDeBruijn (NamedDeBruijn _ ix) = DeBruijn ix

unNameTyDeBruijn
    :: NamedTyDeBruijn -> TyDeBruijn
unNameTyDeBruijn (NamedTyDeBruijn db) = TyDeBruijn $ unNameDeBruijn db

nameToDeBruijn
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => Name -> m NamedDeBruijn
nameToDeBruijn (Name str u) = NamedDeBruijn str <$> getIndex u

tyNameToDeBruijn
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => TyName -> m NamedTyDeBruijn
tyNameToDeBruijn (TyName n) = NamedTyDeBruijn <$> nameToDeBruijn n

deBruijnToName
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => NamedDeBruijn -> m Name
deBruijnToName (NamedDeBruijn str ix) = Name str <$> getUnique ix

deBruijnToTyName
    :: (MonadReader Levels m, MonadError FreeVariableError m)
    => NamedTyDeBruijn -> m TyName
deBruijnToTyName (NamedTyDeBruijn n) = TyName <$> deBruijnToName n
