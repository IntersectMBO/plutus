-- | The user-facing API of the renamer.

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Rename
    ( Rename (..)
    ) where

import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename.Internal
import           Language.PlutusCore.Type

-- | The class of things that can be renamed.
-- I.e. things that are capable of satisfying the global uniqueness condition.
class Rename a where
    -- | Rename 'Unique's so that they're globally unique.
    -- In case there are any free variables, they must be left untouched.
    -- Must always assign new names to bound variables,
    -- so that @rename@ can be used for alpha renaming as well.
    rename :: MonadQuote m => a -> m a

instance HasUnique (tyname ann) TypeUnique => Rename (Type tyname ann) where
    rename = runDirectRenameM . renameTypeM

instance (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique) =>
        Rename (Term tyname name ann) where
    rename = runScopedRenameM . renameTermM

instance (HasUnique (tyname ann) TypeUnique, HasUnique (name ann) TermUnique) =>
        Rename (Program tyname name ann) where
    rename = runScopedRenameM . renameProgramM

instance HasUnique (tyname ann) TypeUnique => Rename (NormalizedType tyname ann) where
    rename = traverse rename
