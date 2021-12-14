-- |
-- Module      : Foundation.Collection
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Different collections (list, vector, string, ..) unified under 1 API.
-- an API to rules them all, and in the darkness bind them.
--
{-# LANGUAGE FlexibleInstances #-}
module Foundation.Collection
    ( BoxedZippable(..)
    , Element
    , InnerFunctor(..)
    , Foldable(..)
    , Fold1able(..)
    , Mappable(..)
    , traverse_
    , mapM_
    , forM
    , forM_
    , Collection(..)
    , and
    , or
    , NonEmpty
    , getNonEmpty
    , nonEmpty
    , nonEmpty_
    , nonEmptyFmap
    , Sequential(..)
    , MutableCollection(..)
    , IndexedCollection(..)
    , KeyedCollection(..)
    , Zippable(..)
    , Buildable(..)
    , build_
    , Builder(..)
    , BuildingState(..)
    , Copy(..)
    ) where

import           Foundation.Collection.Buildable
import           Foundation.Collection.Element
import           Foundation.Collection.Foldable
import           Foundation.Collection.Indexed
import           Foundation.Collection.InnerFunctor
import           Foundation.Collection.Keyed
import           Foundation.Collection.Mutable
import           Foundation.Collection.Collection
import           Foundation.Collection.Sequential
import           Foundation.Collection.Mappable
import           Foundation.Collection.Zippable
import           Foundation.Collection.Copy
