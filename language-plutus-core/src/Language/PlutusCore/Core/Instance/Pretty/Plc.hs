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
import           Language.PlutusCore.Pretty.PrettyM

deriving via CompoundlyPretty (Kind ann)
    instance DefaultPrettyPlcStrategy (Kind ann) =>
        PrettyM PrettyConfigPlc (Kind ann)
deriving via CompoundlyPretty (Type tyname uni ann)
    instance DefaultPrettyPlcStrategy (Type tyname uni ann) =>
        PrettyM PrettyConfigPlc (Type tyname uni ann)
deriving via CompoundlyPretty (Term tyname name uni ann)
    instance DefaultPrettyPlcStrategy (Term tyname name uni ann) =>
        PrettyM PrettyConfigPlc (Term tyname name uni ann)
deriving via CompoundlyPretty (Program tyname name uni ann)
    instance DefaultPrettyPlcStrategy (Program tyname name uni ann) =>
        PrettyM PrettyConfigPlc (Program tyname name uni ann)

instance PrettyM PrettyConfigPlc BuiltinName   where prettyBy _ = pretty
instance PrettyM PrettyConfigPlc (Builtin ann) where prettyBy _ = pretty
