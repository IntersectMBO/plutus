{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Core.Instance.Pretty.Plc () where

import           PlutusPrelude

import           PlutusCore.Core.Instance.Pretty.Classic  ()
import           PlutusCore.Core.Instance.Pretty.Readable ()
import           PlutusCore.Core.Type
import           PlutusCore.Pretty.Plc

deriving via PrettyAny (Kind ann)
    instance DefaultPrettyPlcStrategy (Kind ann) =>
        PrettyBy PrettyConfigPlc (Kind ann)
deriving via PrettyAny (Type tyname uni ann)
    instance DefaultPrettyPlcStrategy (Type tyname uni ann) =>
        PrettyBy PrettyConfigPlc (Type tyname uni ann)
deriving via PrettyAny (Term tyname name uni fun ann)
    instance DefaultPrettyPlcStrategy (Term tyname name uni fun ann) =>
        PrettyBy PrettyConfigPlc (Term tyname name uni fun ann)
deriving via PrettyAny (Program tyname name uni fun ann)
    instance DefaultPrettyPlcStrategy (Program tyname name uni fun ann) =>
        PrettyBy PrettyConfigPlc (Program tyname name uni fun ann)
