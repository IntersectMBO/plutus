{-# LANGUAGE DefaultSignatures #-}
module Foundation.Collection.InnerFunctor
    ( InnerFunctor(..)
    ) where

import Basement.Compat.Base
import Foundation.Collection.Element
import qualified Basement.String as S
import qualified Basement.UArray as UV
import           Basement.BoxedArray (Array)

-- | A monomorphic functor that maps the inner values to values of the same type
class InnerFunctor c where
    imap :: (Element c -> Element c) -> c -> c
    default imap :: (Functor f, Element (f a) ~ a, f a ~ c) => (Element c -> Element c) -> c -> c
    imap = fmap

instance InnerFunctor [a]

instance UV.PrimType ty => InnerFunctor (UV.UArray ty) where
    imap = UV.map

instance InnerFunctor (Array ty)

instance InnerFunctor S.String where
    imap = S.charMap
