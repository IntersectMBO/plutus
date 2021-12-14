-- |
-- Module      : Foundation.Tuple.Nat
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- a Generalized version of Fstable, Sndable, ..
--
-- Using this module is limited to GHC 7.10 and above.
--
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Foundation.Tuple.Nth (Nthable(..)) where

import GHC.TypeLits
import Foundation.Tuple

-- | A generalized version of indexed accessor allowing
-- access to tuples n'th element.
--
-- Indexing starts at 1, as 'fst' is used to get first element.
class KnownNat n => Nthable n a where
    type NthTy n a
    nth :: proxy n -> a -> NthTy n a

--------------------
-- 2 elements tuple
--------------------

instance Nthable 1 (a,b) where
    type NthTy 1 (a,b) = a
    nth _ (a,_) = a
instance Nthable 2 (a,b) where
    type NthTy 2 (a,b) = b
    nth _ (_,b) = b
instance Nthable 1 (Tuple2 a b) where
    type NthTy 1 (Tuple2 a b) = a
    nth _ (Tuple2 a _) = a
instance Nthable 2 (Tuple2 a b) where
    type NthTy 2 (Tuple2 a b) = b
    nth _ (Tuple2 _ b) = b

--------------------
-- 3 elements tuple
--------------------

instance Nthable 1 (a,b,c) where
    type NthTy 1 (a,b,c) = a
    nth _ (a,_,_) = a
instance Nthable 2 (a,b,c) where
    type NthTy 2 (a,b,c) = b
    nth _ (_,b,_) = b
instance Nthable 3 (a,b,c) where
    type NthTy 3 (a,b,c) = c
    nth _ (_,_,c) = c

instance Nthable 1 (Tuple3 a b c) where
    type NthTy 1 (Tuple3 a b c) = a
    nth _ (Tuple3 a _ _) = a
instance Nthable 2 (Tuple3 a b c) where
    type NthTy 2 (Tuple3 a b c) = b
    nth _ (Tuple3 _ b _) = b
instance Nthable 3 (Tuple3 a b c) where
    type NthTy 3 (Tuple3 a b c) = c
    nth _ (Tuple3 _ _ c) = c

--------------------
-- 4 elements tuple
--------------------

instance Nthable 1 (a,b,c,d) where
    type NthTy 1 (a,b,c,d) = a
    nth _ (a,_,_,_) = a
instance Nthable 2 (a,b,c,d) where
    type NthTy 2 (a,b,c,d) = b
    nth _ (_,b,_,_) = b
instance Nthable 3 (a,b,c,d) where
    type NthTy 3 (a,b,c,d) = c
    nth _ (_,_,c,_) = c
instance Nthable 4 (a,b,c,d) where
    type NthTy 4 (a,b,c,d) = d
    nth _ (_,_,_,d) = d

instance Nthable 1 (Tuple4 a b c d) where
    type NthTy 1 (Tuple4 a b c d) = a
    nth _ (Tuple4 a _ _ _) = a
instance Nthable 2 (Tuple4 a b c d) where
    type NthTy 2 (Tuple4 a b c d) = b
    nth _ (Tuple4 _ b _ _) = b
instance Nthable 3 (Tuple4 a b c d) where
    type NthTy 3 (Tuple4 a b c d) = c
    nth _ (Tuple4 _ _ c _) = c
instance Nthable 4 (Tuple4 a b c d) where
    type NthTy 4 (Tuple4 a b c d) = d
    nth _ (Tuple4 _ _ _ d) = d
