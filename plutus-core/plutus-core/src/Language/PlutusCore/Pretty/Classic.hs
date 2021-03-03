-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TypeFamilies    #-}

module Language.PlutusCore.Pretty.Classic
    ( PrettyConfigClassic (..)
    , PrettyClassicBy
    , PrettyClassic
    , prettyClassicDef
    , prettyClassicDebug
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Pretty.ConfigName

-- | Configuration for the classic pretty-printing.
newtype PrettyConfigClassic configName = PrettyConfigClassic
    { _pccConfigName :: configName
    }

type instance HasPrettyDefaults (PrettyConfigClassic _) = 'True

-- | The "classically pretty-printable" constraint.
type PrettyClassicBy configName = PrettyBy (PrettyConfigClassic configName)

type PrettyClassic = PrettyClassicBy PrettyConfigName

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
    toPrettyConfigName = _pccConfigName

-- | Pretty-print a value in the default mode using the classic view.
prettyClassicDef :: PrettyClassic a => a -> Doc ann
prettyClassicDef = prettyBy $ PrettyConfigClassic defPrettyConfigName

-- | Pretty-print a value in the debug mode using the classic view.
prettyClassicDebug :: PrettyClassic a => a -> Doc ann
prettyClassicDebug = prettyBy $ PrettyConfigClassic debugPrettyConfigName
