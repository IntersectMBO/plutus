-- | While the flexible pretty-printing infrastructure is useful when you want it,
-- it's helpful to have an implementation of the default Pretty typeclass that
-- does the default thing.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Core.Instance.Pretty.Default () where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Classic ()
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

instance Pretty (Kind ann) where
    pretty = prettyClassicDef

instance (PrettyClassic (tyname ann), GShow uni) => Pretty (Type tyname uni ann) where
    pretty = prettyClassicDef

instance
        ( PrettyClassic (tyname ann)
        , PrettyClassic (name ann)
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst
        ) => Pretty (Term tyname name uni ann) where
    pretty = prettyClassicDef

instance
        ( PrettyClassic (tyname ann)
        , PrettyClassic (name ann)
        , GShow uni, Closed uni, uni `Everywhere` PrettyConst
        ) => Pretty (Program tyname name uni ann) where
    pretty = prettyClassicDef
