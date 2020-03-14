-- | The global pretty-printing config used to pretty-print everything in the PLC world.
-- This module also defines custom pretty-printing functions for PLC types as a convenience.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Core.Instance.Pretty.Plc () where

import           PlutusPrelude

import           Language.PlutusCore.Core.Instance.Pretty.Classic  ()
import           Language.PlutusCore.Core.Instance.Pretty.Readable ()
import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Pretty.Plc

instance PrettyBy PrettyConfigPlc (Kind ann)
instance DefaultPrettyPlcStrategy (Type tyname uni ann) =>
    PrettyBy PrettyConfigPlc (Type tyname uni ann)
instance DefaultPrettyPlcStrategy (Term tyname name uni ann) =>
    PrettyBy PrettyConfigPlc (Term tyname name uni ann)
instance DefaultPrettyPlcStrategy (Program tyname name uni ann) =>
    PrettyBy PrettyConfigPlc (Program tyname name uni ann)

-- TODO: use @DerivingVia@.
instance PrettyBy PrettyConfigPlc BuiltinName where
    prettyBy _ = pretty
instance PrettyBy PrettyConfigPlc (Builtin ann) where
    prettyBy _ = pretty
