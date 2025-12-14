{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.
module PlutusCore.Pretty.Classic
  ( PrettyConfigClassic (..)
  , PrettyClassicBy
  , PrettyClassic
  , PrettyParens
  , juxtRenderContext
  , consAnnIf
  , prettyConfigClassic
  , prettyConfigClassicSimple
  , prettyClassic
  , prettyClassicSimple
  ) where

import PlutusPrelude

import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.Extra

import Prettyprinter.Internal (Doc (Empty))

-- | Configuration for the classic pretty-printing.
data PrettyConfigClassic configName = PrettyConfigClassic
  { _pccConfigName :: configName
  -- ^ How to pretty-print names.
  , _pccDisplayAnn :: Bool
  -- ^ Whether to display annotations.
  }
  deriving stock (Show)

type instance HasPrettyDefaults (PrettyConfigClassic _) = 'True

-- | The "classically pretty-printable" constraint.
type PrettyClassicBy configName = PrettyBy (PrettyConfigClassic configName)

type PrettyClassic = PrettyClassicBy PrettyConfigName

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
  toPrettyConfigName = _pccConfigName

isEmptyDoc :: Doc ann -> Bool
isEmptyDoc Empty = True
isEmptyDoc _ = False

{-| Add a pretty-printed annotation to a list of 'Doc's if the given config enables pretty-printing
of annotations. -}
consAnnIf :: Pretty ann => PrettyConfigClassic configName -> ann -> [Doc dann] -> [Doc dann]
consAnnIf config ann rest = filter (not . isEmptyDoc) [pretty ann | _pccDisplayAnn config] ++ rest

prettyConfigClassic :: PrettyConfigClassic PrettyConfigName
prettyConfigClassic = PrettyConfigClassic prettyConfigName False

prettyConfigClassicSimple :: PrettyConfigClassic PrettyConfigName
prettyConfigClassicSimple = PrettyConfigClassic prettyConfigNameSimple False

-- | Pretty-print a value in the default mode using the classic view.
prettyClassic :: PrettyClassic a => a -> Doc ann
prettyClassic = prettyBy prettyConfigClassic

-- | Pretty-print a value in the simple mode using the classic view.
prettyClassicSimple :: PrettyClassic a => a -> Doc ann
prettyClassicSimple = prettyBy prettyConfigClassicSimple
