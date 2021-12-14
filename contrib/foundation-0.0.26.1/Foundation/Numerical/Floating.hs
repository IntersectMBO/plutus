{-# LANGUAGE TypeSynonymInstances #-}
module Foundation.Numerical.Floating
    ( FloatingPoint(..)
    ) where

import           Basement.Compat.Base
import           Data.Proxy
import qualified Prelude

-- | IEEE754 Floating Point
class FloatingPoint a where
    floatRadix  :: Proxy a -> Integer
    floatDigits :: Proxy a -> Int
    floatRange  :: Proxy a -> (Int, Int)
    floatDecode :: a -> (Integer, Int)
    floatEncode :: Integer -> Int -> a

instance FloatingPoint Float where
    floatRadix _ = Prelude.floatRadix (0.0 :: Float)
    floatDigits _ = Prelude.floatDigits (0.0 :: Float)
    floatRange _ = Prelude.floatRange (0.0 :: Float)
    floatDecode = Prelude.decodeFloat
    floatEncode = Prelude.encodeFloat

instance FloatingPoint Double where
    floatRadix _ = Prelude.floatRadix (0.0 :: Double)
    floatDigits _ = Prelude.floatDigits (0.0 :: Double)
    floatRange _ = Prelude.floatRange (0.0 :: Double)
    floatDecode = Prelude.decodeFloat
    floatEncode = Prelude.encodeFloat
