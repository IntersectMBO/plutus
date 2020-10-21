module Language.UntypedPlutusCore.Check.Uniques
    ( checkProgram
    , checkTerm
    , UniqueError (..)
    , AsUniqueError (..)
    ) where

import           Language.UntypedPlutusCore.Analysis.Definitions
import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Error
import           Language.PlutusCore.Name

import           Control.Monad.Error.Lens
import           Control.Monad.Except

import           Data.Foldable

checkProgram
    :: (Ord ann,
        HasUnique name TermUnique,
        AsUniqueError e ann,
        MonadError e m)
    => (UniqueError ann -> Bool)
    -> Program name uni ann
    -> m ()
checkProgram p (Program _ _ t) = checkTerm p t

checkTerm
    :: (Ord ann,
        HasUnique name TermUnique,
        AsUniqueError e ann,
        MonadError e m)
    => (UniqueError ann -> Bool)
    -> Term name uni ann
    -> m ()
checkTerm p t = do
    (_, errs) <- runTermDefs t
    for_ errs $ \e -> when (p e) $ throwing _UniqueError e
