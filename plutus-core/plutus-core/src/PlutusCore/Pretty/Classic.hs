-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Pretty.Classic
    ( PrettyConfigClassic (..)
    , PrettyClassicBy
    , PrettyClassic
    , consAnnIf
    , defPrettyConfigClassic
    , debugPrettyConfigClassic
    , prettyClassicDef
    , prettyClassicDebug
    ) where

import PlutusPrelude

import PlutusCore.Pretty.ConfigName

import Prettyprinter.Internal (Doc (Empty))

-- | Configuration for the classic pretty-printing.
data PrettyConfigClassic configName = PrettyConfigClassic
    { _pccConfigName :: configName  -- ^ How to pretty-print names.
    , _pccDisplayAnn :: Bool        -- ^ Whether to display annotations.
    }

type instance HasPrettyDefaults (PrettyConfigClassic _) = 'True

-- | The "classically pretty-printable" constraint.
type PrettyClassicBy configName = PrettyBy (PrettyConfigClassic configName)

type PrettyClassic = PrettyClassicBy PrettyConfigName

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
    toPrettyConfigName = _pccConfigName

isEmptyDoc :: Doc ann -> Bool
isEmptyDoc Empty = True
isEmptyDoc _     = False

-- | Add a pretty-printed annotation to a list of 'Doc's if the given config enables pretty-printing
-- of annotations.
consAnnIf :: Pretty ann => PrettyConfigClassic configName -> ann -> [Doc dann] -> [Doc dann]
consAnnIf config ann rest = filter (not . isEmptyDoc) [pretty ann | _pccDisplayAnn config] ++ rest

defPrettyConfigClassic :: PrettyConfigClassic PrettyConfigName
defPrettyConfigClassic = PrettyConfigClassic defPrettyConfigName False

debugPrettyConfigClassic :: PrettyConfigClassic PrettyConfigName
debugPrettyConfigClassic = PrettyConfigClassic debugPrettyConfigName False

-- | Pretty-print a value in the default mode using the classic view.
prettyClassicDef :: PrettyClassic a => a -> Doc ann
prettyClassicDef = prettyBy defPrettyConfigClassic

-- | Pretty-print a value in the debug mode using the classic view.
prettyClassicDebug :: PrettyClassic a => a -> Doc ann
prettyClassicDebug = prettyBy debugPrettyConfigClassic
