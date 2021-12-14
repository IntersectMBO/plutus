module Foundation.Random.DRG
    ( RandomGen(..)
    , MonadRandomState(..)
    , withRandomGenerator
    ) where

import           Basement.Imports
import           Foundation.Random.Class

-- | A Deterministic Random Generator (DRG) class
class RandomGen gen where
    -- | Initialize a new random generator
    randomNew :: MonadRandom m => m gen

    -- | Initialize a new random generator from a binary seed.
    --
    -- If `Nothing` is returned, then the data is not acceptable
    -- for creating a new random generator.
    randomNewFrom :: UArray Word8 -> Maybe gen

    -- | Generate N bytes of randomness from a DRG
    randomGenerate :: CountOf Word8 -> gen -> (UArray Word8, gen)

    -- | Generate a Word64 from a DRG
    randomGenerateWord64 :: gen -> (Word64, gen)

    randomGenerateF32 :: gen -> (Float, gen)

    randomGenerateF64 :: gen -> (Double, gen)

-- | A simple Monad class very similar to a State Monad
-- with the state being a RandomGenerator.
newtype MonadRandomState gen a = MonadRandomState { runRandomState :: gen -> (a, gen) }

instance Functor (MonadRandomState gen) where
    fmap f m = MonadRandomState $ \g1 ->
        let (a, g2) = runRandomState m g1 in (f a, g2)

instance Applicative (MonadRandomState gen) where
    pure a     = MonadRandomState $ \g -> (a, g)
    (<*>) fm m = MonadRandomState $ \g1 ->
        let (f, g2) = runRandomState fm g1
            (a, g3) = runRandomState m g2
         in (f a, g3)

instance Monad (MonadRandomState gen) where
    return a    = MonadRandomState $ \g -> (a, g)
    (>>=) m1 m2 = MonadRandomState $ \g1 ->
        let (a, g2) = runRandomState m1 g1
         in runRandomState (m2 a) g2

instance RandomGen gen => MonadRandom (MonadRandomState gen) where
    getRandomBytes n = MonadRandomState (randomGenerate n)
    getRandomWord64  = MonadRandomState randomGenerateWord64
    getRandomF32  = MonadRandomState randomGenerateF32
    getRandomF64  = MonadRandomState randomGenerateF64


-- | Run a pure computation with a Random Generator in the 'MonadRandomState'
withRandomGenerator :: RandomGen gen
                    => gen
                    -> MonadRandomState gen a
                    -> (a, gen)
withRandomGenerator gen m = runRandomState m gen
