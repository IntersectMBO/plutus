module PlutusIR.Check.Uniques
  ( checkProgram
  , checkTerm
  , UniqueError (..)
  ) where

import PlutusCore.Error
import PlutusCore.Name.Unique
import PlutusIR.Analysis.Definitions
import PlutusIR.Core

import Control.Monad (when)
import Control.Monad.Except (MonadError, throwError)

import Data.Foldable

checkProgram
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadError (UniqueError ann) m
     )
  => (UniqueError ann -> Bool)
  -> Program tyname name uni fun ann
  -> m ()
checkProgram p (Program _ _ t) = checkTerm p t

checkTerm
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadError (UniqueError ann) m
     )
  => (UniqueError ann -> Bool)
  -> Term tyname name uni fun ann
  -> m ()
checkTerm p t = do
  (_, errs) <- runTermDefs t
  for_ errs $ \e -> when (p e) $ throwError e
