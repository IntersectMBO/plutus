-- | The internal module of the renamer that defines the actual algorithms,
-- but not the user-facing API.

module UntypedPlutusCore.Rename.Internal
    ( module Export
    , renameTermM
    , renameProgramM
    ) where

import           UntypedPlutusCore.Core

import           PlutusCore.Core         (HasUniques)
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Rename.Monad as Export


-- | Rename a 'Term' in the 'RenameM' monad.
renameTermM
    :: (HasUniques (Term name uni fun ann), MonadQuote m)
    => Term name uni fun ann -> ScopedRenameT m (Term name uni fun ann)
renameTermM (LamAbs ann name body)  =
     withFreshenedName name $ \nameFr -> LamAbs ann nameFr <$> renameTermM body
renameTermM (Apply ann fun arg)        = Apply ann <$> renameTermM fun <*> renameTermM arg
renameTermM err@Error{}                = pure err
renameTermM (Var ann name)             = Var ann <$> renameNameM name
renameTermM (Delay ann term)           = Delay ann <$> renameTermM term
renameTermM (Force ann term)           = Force ann <$> renameTermM term
renameTermM con@Constant{}             = pure con
renameTermM bi@Builtin{}               = pure bi

-- | Rename a 'Program' in the 'RenameM' monad.
renameProgramM
    :: (HasUniques (Program name uni fun ann), MonadQuote m)
    => Program name uni fun ann -> ScopedRenameT m (Program name uni fun ann)
renameProgramM (Program ann ver term) = Program ann ver <$> renameTermM term
