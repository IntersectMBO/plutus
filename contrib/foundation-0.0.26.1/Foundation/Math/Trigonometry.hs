{-# LANGUAGE TypeSynonymInstances #-}
module Foundation.Math.Trigonometry
    ( Trigonometry(..)
    ) where

import           Basement.Compat.Base
import qualified Prelude

-- | Method to support basic trigonometric functions
class Trigonometry a where
    -- | the famous pi value
    pi    :: a
    -- | sine
    sin   :: a -> a
    -- | cosine
    cos   :: a -> a
    -- | tan
    tan   :: a -> a
    -- | sine-1
    asin  :: a -> a
    -- | cosine-1
    acos  :: a -> a
    -- | tangent-1
    atan  :: a -> a
    -- | hyperbolic sine
    sinh  :: a -> a
    -- | hyperbolic cosine
    cosh  :: a -> a
    -- | hyperbolic tangent
    tanh  :: a -> a
    -- | hyperbolic sine-1
    asinh :: a -> a
    -- | hyperbolic cosine-1
    acosh :: a -> a
    -- | hyperbolic tangent-1
    atanh :: a -> a

instance Trigonometry Float where
    pi = Prelude.pi
    sin = Prelude.sin
    cos = Prelude.cos
    tan = Prelude.tan
    asin = Prelude.asin
    acos = Prelude.acos
    atan = Prelude.atan
    sinh = Prelude.sinh
    cosh = Prelude.cosh
    tanh = Prelude.tanh
    asinh = Prelude.asinh
    acosh = Prelude.acosh
    atanh = Prelude.atanh

instance Trigonometry Double where
    pi = Prelude.pi
    sin = Prelude.sin
    cos = Prelude.cos
    tan = Prelude.tan
    asin = Prelude.asin
    acos = Prelude.acos
    atan = Prelude.atan
    sinh = Prelude.sinh
    cosh = Prelude.cosh
    tanh = Prelude.tanh
    asinh = Prelude.asinh
    acosh = Prelude.acosh
    atanh = Prelude.atanh
