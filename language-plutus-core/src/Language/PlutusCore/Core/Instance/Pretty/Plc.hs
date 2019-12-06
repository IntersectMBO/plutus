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
instance PrettyBy PrettyConfigPlc (Builtin ann)
instance DefaultPrettyPlcStrategy (Type tyname ann) =>
    PrettyBy PrettyConfigPlc (Type tyname ann)
instance DefaultPrettyPlcStrategy (Term tyname name ann) =>
    PrettyBy PrettyConfigPlc (Term tyname name ann)
instance DefaultPrettyPlcStrategy (Program tyname name ann) =>
    PrettyBy PrettyConfigPlc (Program tyname name ann)

-- TODO: use @DerivingVia@.
instance PrettyBy PrettyConfigPlc BuiltinName where
    prettyBy _ = pretty
