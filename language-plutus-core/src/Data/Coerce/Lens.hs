{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Coerce.Lens
    ( Unwrap
    , Newtype
    , coerced
    , wrapped
    , unwrapped
    ) where

import           Data.Coerce
import           GHC.Generics
import           Lens.Micro

type family UnwrapRep r :: * where
    UnwrapRep (D1 d (C1 c (S1 s (K1 i a)))) = a

-- | Extract the underlying type of a newtype wrapper.
type Unwrap a = UnwrapRep (Rep a)

-- | The "is a newtype" constaint.
type Newtype new = Coercible (Unwrap new) new

-- | The lens induced by back and forth coercions.
coerced :: Coercible a b => Lens' a b
coerced f x = coerce <$> f (coerce x)

-- | A specialized version of 'coerced' that works over newtypes.
-- Useful, because improves type inference.
wrapped :: Newtype new => Lens' new (Unwrap new)
wrapped = coerced

-- | A specialized version of 'coerced' that works over newtypes.
-- Useful, because improves type inference.
unwrapped :: Newtype new => Lens' (Unwrap new) new
unwrapped = coerced
