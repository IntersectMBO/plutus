module Foundation.Random.Class
    ( MonadRandom(..)
    ) where

import           Data.Proxy
import           Basement.Imports
import           Foundation.System.Entropy
import qualified Basement.UArray as A

-- | A monad constraint that allows to generate random bytes
class (Functor m, Applicative m, Monad m) => MonadRandom m where
    getRandomBytes :: CountOf Word8 -> m (UArray Word8)
    getRandomWord64 :: m Word64
    getRandomF32 :: m Float
    getRandomF64 :: m Double

instance MonadRandom IO where
    getRandomBytes  = getEntropy
    getRandomWord64 = flip A.index 0 . A.unsafeRecast
                  <$> getRandomBytes (A.primSizeInBytes (Proxy :: Proxy Word64))
    getRandomF32 = flip A.index 0 . A.unsafeRecast
                  <$> getRandomBytes (A.primSizeInBytes (Proxy :: Proxy Word64))
    getRandomF64 = flip A.index 0 . A.unsafeRecast
                  <$> getRandomBytes (A.primSizeInBytes (Proxy :: Proxy Word64))
