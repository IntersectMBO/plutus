-- Extra bits stuff
module Foundation.Bits
    ( (.<<.)
    , (.>>.)
    , Bits(..)
    , alignRoundUp
    , alignRoundDown
    ) where

import Basement.Compat.Base
import Foundation.Numerical
import Data.Bits

-- | Unsafe Shift Left Operator
(.<<.) :: Bits a => a -> Int -> a
(.<<.) = unsafeShiftL

-- | Unsafe Shift Right Operator
(.>>.) :: Bits a => a -> Int -> a
(.>>.) = unsafeShiftR

-- | Round up (if needed) to a multiple of @alignment@ closst to @m@
--
-- @alignment@ needs to be a power of two
--
-- alignRoundUp 16 8 = 16
-- alignRoundUp 15 8 = 16
alignRoundUp :: Int -- ^ Number to Align
             -> Int -- ^ Alignment (power of 2)
             -> Int
alignRoundUp m alignment = (m + (alignment-1)) .&. complement (alignment-1)

-- | Round down (if needed) to a multiple of @alignment@ closest to @m@
--
-- @alignment@ needs to be a power of two
--
-- > alignRoundDown 15 8 = 8
-- > alignRoundDown 8 8  = 8
alignRoundDown :: Int -- ^ Number to Align
               -> Int -- ^ Alignment (power of 2)
               -> Int
alignRoundDown m alignment = m .&. complement (alignment-1)
