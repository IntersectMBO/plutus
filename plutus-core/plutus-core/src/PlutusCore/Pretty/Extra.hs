{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Pretty.Extra () where

import PlutusPrelude

import Data.Map (Map)
import Data.Map qualified as Map
import Text.PrettyBy.Internal

instance PrettyDefaultBy config [(k, v)] => DefaultPrettyBy config (Map k v) where
    defaultPrettyBy config = prettyBy config . Map.toList

deriving via PrettyCommon (Map k v)
    instance PrettyDefaultBy config (Map k v) => PrettyBy config (Map k v)
