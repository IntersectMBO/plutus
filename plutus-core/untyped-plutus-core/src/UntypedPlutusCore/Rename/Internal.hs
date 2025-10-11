-- | The internal module of the renamer that defines the actual algorithms,
-- but not the user-facing API.

{-# LANGUAGE ConstraintKinds #-}

module UntypedPlutusCore.Rename.Internal
    ( module Export
    , renameTermM
    , renameProgramM
    ) where

import UntypedPlutusCore.Core

import PlutusCore.Core (HasUniques)
import PlutusCore.Name.Unique
import PlutusCore.Quote
import PlutusCore.Rename.Monad as Export

import Control.Monad.Reader (MonadReader)

type MonadRename m = (MonadQuote m, MonadReader (Renaming TermUnique) m)

-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (MonadRename m, HasUniques (Term name uni fun ann))
    => Term name uni fun ann -> m (Term name uni fun ann)
renameTermM (LamAbs ann name body)  =
     withFreshenedName name $ \nameFr -> LamAbs ann nameFr <$> renameTermM body
renameTermM (Apply ann fun arg)        = Apply ann <$> renameTermM fun <*> renameTermM arg
renameTermM err@Error{}                = pure err
renameTermM (Var ann name)             = Var ann <$> renameNameM name
renameTermM (Delay ann term)           = Delay ann <$> renameTermM term
renameTermM (Force ann term)           = Force ann <$> renameTermM term
renameTermM (Constr ann i es)          = Constr ann i <$> traverse renameTermM es
renameTermM (Case ann arg cs)          = Case ann <$> renameTermM arg <*> traverse renameTermM cs
renameTermM con@Constant{}             = pure con
renameTermM bi@Builtin{}               = pure bi
renameTermM (Let ann names body)       =
  let
    goNames acc []     = Let ann (acc []) <$> renameTermM body
    goNames acc (n:ns) = withFreshenedName n $ \n' -> goNames (acc . (n':)) ns
  in goNames id names
renameTermM (Bind ann t binds) = Bind ann <$> renameTermM t <*> traverse renameTermM binds

-- | Rename a 'Program' in the 'RenameM' monad.
renameProgramM
    :: (MonadRename m, HasUniques (Program name uni fun ann))
    => Program name uni fun ann -> m (Program name uni fun ann)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term
