-- | While the flexible pretty-printing infrastructure is useful when you want it,
-- it's helpful to have an implementation of the default Pretty typeclass that
-- does the default thing.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Core.Instance.Pretty.Default () where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Classic ()
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Pretty.Classic

instance Pretty (Kind ann) where
    pretty = prettyClassicDef
instance Pretty (Constant ann) where
    pretty = prettyClassicDef
instance Pretty (Builtin ann) where
    pretty = prettyClassicDef
instance PrettyClassic (tyname ann) => Pretty (Type tyname ann) where
    pretty = prettyClassicDef
instance (PrettyClassic (tyname ann), PrettyClassic (name ann)) => Pretty (Term tyname name ann) where
    pretty = prettyClassicDef
instance (PrettyClassic (tyname ann), PrettyClassic (name ann)) => Pretty (Program tyname name ann) where
    pretty = prettyClassicDef
