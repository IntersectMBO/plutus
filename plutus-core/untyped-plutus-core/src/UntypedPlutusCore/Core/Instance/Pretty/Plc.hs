{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Core.Instance.Pretty.Plc () where

import PlutusPrelude

import UntypedPlutusCore.Core.Instance.Pretty.Classic ()
import UntypedPlutusCore.Core.Instance.Pretty.Readable ()
import UntypedPlutusCore.Core.Type

import PlutusCore.Pretty.Plc

deriving via
  PrettyAny (Term name uni fun pat ann)
  instance
    DefaultPrettyPlcStrategy (Term name uni fun pat ann)
    => PrettyBy PrettyConfigPlc (Term name uni fun pat ann)
deriving via
  PrettyAny (Program name uni fun pat ann)
  instance
    DefaultPrettyPlcStrategy (Program name uni fun pat ann)
    => PrettyBy PrettyConfigPlc (Program name uni fun pat ann)
