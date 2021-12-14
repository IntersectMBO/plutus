-- |
-- Module      : Foundation.Tuple
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
module Foundation.Tuple
    ( Tuple2(..)
    , Tuple3(..)
    , Tuple4(..)
    , Fstable(..)
    , Sndable(..)
    , Thdable(..)
    ) where

import Basement.Compat.Base
import Basement.Compat.Bifunctor
import Foundation.Primitive

-- | Strict tuple (a,b)
data Tuple2 a b = Tuple2 !a !b
    deriving (Show,Eq,Ord,Typeable,Data,Generic)

instance (NormalForm a, NormalForm b) => NormalForm (Tuple2 a b) where
    toNormalForm (Tuple2 a b) = toNormalForm a `seq` toNormalForm b
instance Bifunctor Tuple2 where
  bimap f g (Tuple2 a b) = Tuple2 (f a) (g b)

-- | Strict tuple (a,b,c)
data Tuple3 a b c = Tuple3 !a !b !c
    deriving (Show,Eq,Ord,Typeable,Data,Generic)

instance (NormalForm a, NormalForm b, NormalForm c) => NormalForm (Tuple3 a b c) where
    toNormalForm (Tuple3 a b c) = toNormalForm a `seq` toNormalForm b `seq` toNormalForm c

-- | Strict tuple (a,b,c,d)
data Tuple4 a b c d = Tuple4 !a !b !c !d
    deriving (Show,Eq,Ord,Typeable,Data,Generic)

instance (NormalForm a, NormalForm b, NormalForm c, NormalForm d)
      => NormalForm (Tuple4 a b c d) where
    toNormalForm (Tuple4 a b c d) = toNormalForm a `seq` toNormalForm b `seq` toNormalForm c `seq` toNormalForm d

-- | Class of product types that have a first element
class Fstable a where
    type ProductFirst a
    fst :: a -> ProductFirst a

-- | Class of product types that have a second element
class Sndable a where
    type ProductSecond a
    snd :: a -> ProductSecond a

-- | Class of product types that have a third element
class Thdable a where
    type ProductThird a
    thd :: a -> ProductThird a

instance Fstable (a,b) where
    type ProductFirst (a,b) = a
    fst (a,_) = a
instance Fstable (a,b,c) where
    type ProductFirst (a,b,c) = a
    fst (a,_,_) = a
instance Fstable (a,b,c,d) where
    type ProductFirst (a,b,c,d) = a
    fst (a,_,_,_) = a
instance Fstable (Tuple2 a b) where
    type ProductFirst (Tuple2 a b) = a
    fst (Tuple2 a _) = a
instance Fstable (Tuple3 a b c) where
    type ProductFirst (Tuple3 a b c) = a
    fst (Tuple3 a _ _) = a
instance Fstable (Tuple4 a b c d) where
    type ProductFirst (Tuple4 a b c d) = a
    fst (Tuple4 a _ _ _) = a

instance Sndable (a,b) where
    type ProductSecond (a,b) = b
    snd (_,b) = b
instance Sndable (a,b,c) where
    type ProductSecond (a,b,c) = b
    snd (_,b,_) = b
instance Sndable (a,b,c,d) where
    type ProductSecond (a,b,c,d) = b
    snd (_,b,_,_) = b
instance Sndable (Tuple2 a b) where
    type ProductSecond (Tuple2 a b) = b
    snd (Tuple2 _ b) = b
instance Sndable (Tuple3 a b c) where
    type ProductSecond (Tuple3 a b c) = b
    snd (Tuple3 _ b _) = b
instance Sndable (Tuple4 a b c d) where
    type ProductSecond (Tuple4 a b c d) = b
    snd (Tuple4 _ b _ _) = b

instance Thdable (a,b,c) where
    type ProductThird (a,b,c) = c
    thd (_,_,c) = c
instance Thdable (a,b,c,d) where
    type ProductThird (a,b,c,d) = c
    thd (_,_,c,_) = c
instance Thdable (Tuple3 a b c) where
    type ProductThird (Tuple3 a b c) = c
    thd (Tuple3 _ _ c) = c
instance Thdable (Tuple4 a b c d) where
    type ProductThird (Tuple4 a b c d) = c
    thd (Tuple4 _ _ c _) = c
