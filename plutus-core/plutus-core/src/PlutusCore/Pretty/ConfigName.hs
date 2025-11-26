{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusCore.Pretty.ConfigName
  ( PrettyConfigName (..)
  , HasPrettyConfigName (..)
  , prettyConfigName
  , prettyConfigNameSimple
  ) where

import Data.Coerce (coerce)
import Text.PrettyBy (HasPrettyDefaults)
import Text.PrettyBy.Fixity (Sole (Sole))

-- | A config that determines how to pretty-print a PLC name.
newtype PrettyConfigName = PrettyConfigName
  { _pcnShowsUnique :: Bool
  -- ^ Whether to show the 'Unique' of a name or not.
  }
  deriving stock (Eq, Show)

type instance HasPrettyDefaults PrettyConfigName = 'True

-- | A class of configs from which a 'PrettyConfigName' can be extracted.
class HasPrettyConfigName config where
  toPrettyConfigName :: config -> PrettyConfigName

instance HasPrettyConfigName (Sole PrettyConfigName) where
  toPrettyConfigName = coerce

-- | The 'PrettyConfigName' used by default: print 'Unique' indexes after nams.
prettyConfigName :: PrettyConfigName
prettyConfigName = PrettyConfigName {_pcnShowsUnique = True}

-- | The 'PrettyConfigName' to be used when 'Unique' indices don't matter. Easier to read.
prettyConfigNameSimple :: PrettyConfigName
prettyConfigNameSimple = PrettyConfigName {_pcnShowsUnique = False}
