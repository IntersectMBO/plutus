{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-deriving-strategies #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    , TypeF (..)
    , KindF (..)
    ) where

import PlutusCore.Core.Type
import PlutusPrelude

import Data.Functor.Foldable.TH

$(join <$> traverse makeBaseFunctor [''Kind, ''Type, ''Term])
