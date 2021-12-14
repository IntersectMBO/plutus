-- |
-- Module      : Foundation.Numerical
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Compared to the Haskell hierarchy of number classes
-- this provide a more flexible approach that is closer to the
-- mathematical foundation (group, field, etc)
--
-- This try to only provide one feature per class, at the expense of
-- the number of classes.
--
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Foundation.Numerical
    ( IsIntegral(..)
    , IsNatural(..)
    , Signed(..)
    , Additive(..)
    , Subtractive(..)
    , Multiplicative(..)
    , IDivisible(..)
    , Divisible(..)
    , Sign(..)
    , recip
    , IntegralRounding(..)
    , FloatingPoint(..)
    ) where

import           Basement.Compat.Base
import           Basement.Numerical.Number
import           Basement.Numerical.Additive
import           Basement.Numerical.Subtractive
import           Basement.Numerical.Multiplicative
import           Foundation.Numerical.Floating
import qualified Prelude

-- | Sign of a signed number
data Sign = SignNegative | SignZero | SignPositive
    deriving (Eq)

orderingToSign :: Ordering -> Sign
orderingToSign EQ = SignZero
orderingToSign GT = SignNegative
orderingToSign LT = SignPositive

-- | types that have sign and can be made absolute
class Signed a where
    {-# MINIMAL abs, signum #-}
    abs    :: a -> a
    signum :: a -> Sign

instance Signed Integer where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Int where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Int8 where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Int16 where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Int32 where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Int64 where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Float where
    abs = Prelude.abs
    signum = orderingToSign . compare 0
instance Signed Double where
    abs = Prelude.abs
    signum = orderingToSign . compare 0

class IntegralRounding a where
    -- | Round up, to the next integral.
    --
    -- Also known as 'ceiling'
    roundUp       :: Integral n => a -> n

    -- | Round down, to the previous integral
    --
    -- Also known as 'floor'
    roundDown     :: Integral n => a -> n

    -- | Truncate to the closest integral to the fractional number
    -- closer to 0.
    --
    -- This is equivalent to roundUp for negative Number
    -- and roundDown for positive Number
    roundTruncate :: Integral n => a -> n

    -- | Round to the nearest integral
    --
    -- > roundNearest 3.6
    -- 4
    -- > roundNearest 3.4
    -- 3
    roundNearest  :: Integral n => a -> n

instance IntegralRounding Prelude.Rational where
    roundUp       = fromInteger . Prelude.ceiling
    roundDown     = fromInteger . Prelude.floor
    roundTruncate = fromInteger . Prelude.truncate
    roundNearest  = fromInteger . Prelude.round

instance IntegralRounding Prelude.Double where
    roundUp       = fromInteger . Prelude.ceiling
    roundDown     = fromInteger . Prelude.floor
    roundTruncate = fromInteger . Prelude.truncate
    roundNearest  = fromInteger . Prelude.round

instance IntegralRounding Prelude.Float where
    roundUp       = fromInteger . Prelude.ceiling
    roundDown     = fromInteger . Prelude.floor
    roundTruncate = fromInteger . Prelude.truncate
    roundNearest  = fromInteger . Prelude.round
