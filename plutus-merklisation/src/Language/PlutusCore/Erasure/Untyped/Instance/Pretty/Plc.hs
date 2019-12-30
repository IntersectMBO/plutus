-- | The global pretty-printing config used to pretty-print everything in the PLC world.
-- This module also defines custom pretty-printing functions for PLC types as a convenience.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Plc () where

import           PlutusPrelude

import           Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Classic  ()
import           Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Readable ()
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Pretty.Plc

instance DefaultPrettyPlcStrategy (Term name ann) =>
    PrettyBy PrettyConfigPlc (Term name ann)
instance DefaultPrettyPlcStrategy (Program name ann) =>
    PrettyBy PrettyConfigPlc (Program name ann)

