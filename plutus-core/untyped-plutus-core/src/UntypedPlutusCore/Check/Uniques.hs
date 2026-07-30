module UntypedPlutusCore.Check.Uniques
  ( checkProgram
  , checkTerm
  , UniqueError (..)
  ) where

import UntypedPlutusCore.Analysis.Definitions
import UntypedPlutusCore.Core

import PlutusCore.Error
import PlutusCore.Name.Unique

import Control.Monad (when)
import Control.Monad.Except

import Data.Foldable

checkProgram
  :: ( Ord ann
     , HasUnique name TermUnique
     , MonadError (UniqueError ann) m
     )
  => (UniqueError ann -> Bool)
  -> Program name uni fun ann
  -> m ()
checkProgram p (Program _ _ t) = checkTerm p t

checkTerm
  :: ( Ord ann
     , HasUnique name TermUnique
     , MonadError (UniqueError ann) m
     )
  => (UniqueError ann -> Bool)
  -> Term name uni fun ann
  -> m ()
checkTerm p t = do
  (_, errs) <- runTermDefs t
  for_ errs $ \e -> when (p e) $ throwError e
