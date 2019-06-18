module Language.PlutusCore.Check.Uniques (
    checkProgram
    , checkTerm
    , checkType
    , UniqueError (..)
    , AsUniqueError (..)) where

import           Language.PlutusCore.Analysis.Definitions
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

import           Control.Monad.Error.Lens
import           Control.Monad.Except

import           Data.Foldable

checkProgram
    :: (Ord a,
        HasUnique (name a) TermUnique,
        HasUnique (tyname a) TypeUnique,
        AsUniqueError e a,
        MonadError e m)
    => (UniqueError a -> Bool)
    -> Program tyname name a
    -> m ()
checkProgram p (Program _ _ t) = checkTerm p t

checkTerm
    :: (Ord a,
        HasUnique (name a) TermUnique,
        HasUnique (tyname a) TypeUnique,
        AsUniqueError e a,
        MonadError e m)
    => (UniqueError a -> Bool)
    -> Term tyname name a
    -> m ()
checkTerm p t = do
    (_, errs) <- runTermDefs t
    for_ errs $ \e -> when (p e) $ throwing _UniqueError e

checkType
    :: (Ord a,
        HasUnique (tyname a) TypeUnique,
        AsUniqueError e a,
        MonadError e m)
    => (UniqueError a -> Bool)
    -> Type tyname a
    -> m ()
checkType p t = do
    (_, errs) <- runTypeDefs t
    for_ errs $ \e -> when (p e) $ throwing _UniqueError e
