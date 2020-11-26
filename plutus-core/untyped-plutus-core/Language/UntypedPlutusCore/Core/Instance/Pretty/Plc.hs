{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.UntypedPlutusCore.Core.Instance.Pretty.Plc () where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core.Instance.Pretty.Classic  ()
import           Language.UntypedPlutusCore.Core.Instance.Pretty.Readable ()
import           Language.UntypedPlutusCore.Core.Type

import           Language.PlutusCore.Pretty.Plc

deriving via PrettyAny (Term name uni fun ann)
    instance DefaultPrettyPlcStrategy (Term name uni fun ann) =>
        PrettyBy PrettyConfigPlc (Term name uni fun ann)
deriving via PrettyAny (Program name uni fun ann)
    instance DefaultPrettyPlcStrategy (Program name uni fun ann) =>
        PrettyBy PrettyConfigPlc (Program name uni fun ann)
