{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

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

import           Control.Lens
import           Data.Functor.Foldable.TH
import           Language.PlutusCore.Name

$(join <$> traverse makeBaseFunctor [''Kind, ''Type, ''Term])

instance Plated (Term TyName Name uni fun a) where
  plate = gplate
