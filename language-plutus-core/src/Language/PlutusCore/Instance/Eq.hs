-- | 'Eq' instances for core data types.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Instance.Eq () where

import           Language.PlutusCore.Instance.Eq.Internal
import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad
import           Language.PlutusCore.Type

instance HasUniques (Type tyname ann) => Eq (Type tyname ann) where
    ty1 == ty2 = runEqRename @TypeRenaming $ eqTypeM ty1 ty2

instance HasUniques (Term tyname name ann) => Eq (Term tyname name ann) where
    term1 == term2 = runEqRename $ eqTermM term1 term2

instance HasUniques (Program tyname name ann) => Eq (Program tyname name ann) where
    prog1 == prog2 = runEqRename $ eqProgramM prog1 prog2
