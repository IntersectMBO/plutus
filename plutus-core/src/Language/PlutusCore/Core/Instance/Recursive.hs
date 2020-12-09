{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.Core.Instance.Recursive
    ( -- * Base functors
      TermF (..)
    , TypeF (..)
    , KindF (..)
    ) where

import           Language.PlutusCore.Core.Type
import           PlutusPrelude

import           Data.Functor.Foldable.TH

$(join <$> traverse makeBaseFunctor [''Kind, ''Type, ''Term])
