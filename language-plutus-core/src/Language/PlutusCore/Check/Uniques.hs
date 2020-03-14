module Language.PlutusCore.Check.Uniques
    ( checkProgram
    , checkTerm
    , checkType
    , UniqueError (..)
    , AsUniqueError (..)
    ) where

import           Language.PlutusCore.Analysis.Definitions
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Name

import           Control.Monad.Error.Lens
import           Control.Monad.Except

import           Data.Foldable

checkProgram
    :: (Ord ann,
        HasUnique (name ann) TermUnique,
        HasUnique (tyname ann) TypeUnique,
        AsUniqueError e ann,
        MonadError e m)
    => (UniqueError ann -> Bool)
    -> Program tyname name uni ann
    -> m ()
checkProgram p (Program _ _ t) = checkTerm p t

checkTerm
    :: (Ord ann,
        HasUnique (name ann) TermUnique,
        HasUnique (tyname ann) TypeUnique,
        AsUniqueError e ann,
        MonadError e m)
    => (UniqueError ann -> Bool)
    -> Term tyname name uni ann
    -> m ()
checkTerm p t = do
    (_, errs) <- runTermDefs t
    for_ errs $ \e -> when (p e) $ throwing _UniqueError e

checkType
    :: (Ord ann,
        HasUnique (tyname ann) TypeUnique,
        AsUniqueError e ann,
        MonadError e m)
    => (UniqueError ann -> Bool)
    -> Type tyname uni ann
    -> m ()
checkType p t = do
    (_, errs) <- runTypeDefs t
    for_ errs $ \e -> when (p e) $ throwing _UniqueError e
