{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Pretty.Extra () where

import PlutusPrelude

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Text.PrettyBy.Internal

instance PrettyDefaultBy config [(k, v)] => DefaultPrettyBy config (Map k v) where
    defaultPrettyBy config = prettyBy config . Map.toList
deriving via PrettyCommon (Map k v)
    instance PrettyDefaultBy config (Map k v) => PrettyBy config (Map k v)

instance PrettyDefaultBy config [a] => DefaultPrettyBy config (Set a) where
    defaultPrettyBy config = prettyBy config . Set.toList
deriving via PrettyCommon (Set a)
    instance PrettyDefaultBy config (Set a) => PrettyBy config (Set a)
