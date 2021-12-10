{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
-- | Support for using de Bruijn indices for term and type names.
module PlutusCore.DeBruijn.Internal
    ( Index (..)
    , DeBruijn (..)
    , NamedDeBruijn (..)
    , TyDeBruijn (..)
    , NamedTyDeBruijn (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , Level (..)
    , Levels (..)
    , declareUnique
    , declareBinder
    , withScope
    , getIndex
    , getUnique
    , unNameDeBruijn
    , unNameTyDeBruijn
    , fakeNameDeBruijn
    , nameToDeBruijn
    , tyNameToDeBruijn
    , deBruijnToName
    , deBruijnToTyName
    , HasIndex (..)
    ) where

import PlutusCore.Name
import PlutusCore.Pretty
import PlutusCore.Quote

import Control.Exception
import Control.Lens hiding (Index, Level, index, ix)
import Control.Monad.Error.Lens
import Control.Monad.Except
import Control.Monad.Reader

import Data.Bimap qualified as BM
import Data.Text qualified as T
import Prettyprinter

import Numeric.Natural

import Control.DeepSeq (NFData)
import ErrorCode
import GHC.Generics

-- | A relative index used for de Bruijn identifiers.
newtype Index = Index Natural
    deriving stock Generic
    deriving newtype (Show, Num, Enum, Real, Integral, Eq, Ord, Pretty)
    deriving anyclass NFData

-- | A term name as a de Bruijn index.
data NamedDeBruijn = NamedDeBruijn { ndbnString :: T.Text, ndbnIndex :: Index }
    deriving (Show, Generic)
    deriving anyclass NFData

-- | A term name as a de Bruijn index, without the name string.
newtype DeBruijn = DeBruijn { dbnIndex :: Index }
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
newtype Level = Level Integer deriving newtype (Eq, Ord, Num)

-- | During visiting the AST we hold a reader "state" of current level and a current scoping (levelMapping).
-- Invariant-A: the current level is positive and greater than all levels in the levelMapping.
-- Invariant-B: only positive levels are stored in the levelMapping.
data Levels = Levels
            { currentLevel :: Level
            , levelMapping :: BM.Bimap Unique Level
            }

-- | Declare a name with a unique, recording the mapping to a 'Level'.
declareUnique :: (MonadReader Levels m, HasUnique name unique) => name -> m a -> m a
declareUnique n =
    local $ \(Levels current ls) -> Levels current $ BM.insert (n ^. theUnique) current ls

{-| Declares a new binder by assigning a fresh unique to the *current level*.
Maintains invariant-B of 'Levels' (that only positive levels are stored),
since current level is always positive (invariant-A).
See NOTE: [DeBruijn indices of Binders]
-}
declareBinder :: (MonadReader Levels m, MonadQuote m) => m a -> m a
declareBinder act = do
    newU <- freshUnique
    local (\(Levels current ls) -> Levels current $ BM.insert newU current ls) act

-- | Enter a scope, incrementing the current 'Level' by one
-- Maintains invariant-A (that the current level is positive).
withScope :: MonadReader Levels m => m a -> m a
withScope = local $ \(Levels current ls) -> Levels (current+1) ls

-- | We cannot do a correct translation to or from de Bruijn indices if the program is not well-scoped.
-- So we throw an error in such a case.
data FreeVariableError
    = FreeUnique Unique
    | FreeIndex Index
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Exception, NFData)


instance Pretty FreeVariableError where
    pretty (FreeUnique u) = "Free unique:" <+> pretty u
    pretty (FreeIndex i)  = "Free index:" <+> pretty i
makeClassyPrisms ''FreeVariableError

instance HasErrorCode FreeVariableError where
    errorCode  FreeIndex {}  = ErrorCode 23
    errorCode  FreeUnique {} = ErrorCode 22

-- | Get the 'Index' corresponding to a given 'Unique'.
getIndex :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m) => Unique -> m Index
getIndex u = do
    Levels current ls <- ask
    case BM.lookup u ls of
        Just foundlvl -> pure $ levelToIx current foundlvl
        Nothing       -> throwing _FreeVariableError $ FreeUnique u
  where
    -- Compute the relative 'Index' of a absolute 'Level' relative to the current 'Level'.
    levelToIx :: Level -> Level -> Index
    levelToIx (Level current) (Level foundLvl) =
        -- Thanks to invariant-A, we can be sure that 'level >= foundLvl ', since foundLvl is in the levelMapping
        -- and thus the computation 'current-foundLvl' is '>=0' and its conversion to Natural will not lead to arithmetic underflow.
        fromIntegral $ current - foundLvl

-- | Get the 'Unique' corresponding to a given 'Index'.
getUnique :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m) => Index -> m Unique
getUnique ix = do
    Levels current ls <- ask
    case BM.lookupR (ixToLevel current ix) ls of
        Just u  -> pure u
        -- Because of invariant-B, the levelMapping contains only positive levels;
        -- the lookup(negativeLvl) will fail by throwing a free variable error.
        Nothing -> throwing _FreeVariableError $ FreeIndex ix
  where
    -- Compute the absolute 'Level' of a relative 'Index' relative to the current 'Level'.
    -- The index `ixAST` may be malformed or point to a free variable because it comes straight from the AST;
    -- in such a case, this function may return a negative level.
    ixToLevel :: Level -> Index -> Level
    ixToLevel (Level current) ixAST = Level (current - fromIntegral ixAST)


unNameDeBruijn
    :: NamedDeBruijn -> DeBruijn
unNameDeBruijn (NamedDeBruijn _ ix) = DeBruijn ix

unNameTyDeBruijn
    :: NamedTyDeBruijn -> TyDeBruijn
unNameTyDeBruijn (NamedTyDeBruijn db) = TyDeBruijn $ unNameDeBruijn db

fakeNameDeBruijn
    :: DeBruijn -> NamedDeBruijn
fakeNameDeBruijn (DeBruijn ix) = NamedDeBruijn "i" ix

nameToDeBruijn
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => Name -> m NamedDeBruijn
nameToDeBruijn (Name str u) = NamedDeBruijn str <$> getIndex u

tyNameToDeBruijn
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => TyName -> m NamedTyDeBruijn
tyNameToDeBruijn (TyName n) = NamedTyDeBruijn <$> nameToDeBruijn n

deBruijnToName
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => NamedDeBruijn -> m Name
deBruijnToName (NamedDeBruijn str ix) = Name str <$> getUnique ix

deBruijnToTyName
    :: (MonadReader Levels m, AsFreeVariableError e, MonadError e m)
    => NamedTyDeBruijn -> m TyName
deBruijnToTyName (NamedTyDeBruijn n) = TyName <$> deBruijnToName n
