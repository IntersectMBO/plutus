{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module Foundation.Check.Gen
    ( Gen
    , runGen
    , GenParams(..)
    , GenRng
    , genRng
    , genWithRng
    , genWithParams
    ) where

import           Basement.Imports
import           Foundation.Collection
import           Foundation.Random
import qualified Foundation.Random.XorShift as XorShift
import           Foundation.String
import           Foundation.Numerical
import           Foundation.Hashing.SipHash
import           Foundation.Hashing.Hasher

data GenParams = GenParams
    { genMaxSizeIntegral :: Word -- maximum number of bytes
    , genMaxSizeArray    :: Word -- number of elements, as placeholder
    , genMaxSizeString   :: Word -- maximum number of chars
    }

newtype GenRng = GenRng XorShift.State

type GenSeed = Word64

genRng :: GenSeed -> [String] -> (Word64 -> GenRng)
genRng seed groups = \iteration -> GenRng $ XorShift.initialize rngSeed (rngSeed * iteration)
  where
    (SipHash rngSeed) = hashEnd $ hashMixBytes hashData iHashState
    hashData = toBytes UTF8 $ intercalate "::" groups
    iHashState :: Sip1_3
    iHashState = hashNewParam (SipKey seed 0x12345678)

genGenerator :: GenRng -> (GenRng, GenRng)
genGenerator (GenRng rng) =
    let (newSeed1, rngNext) = randomGenerateWord64 rng
        (newSeed2, rngNext') = randomGenerateWord64 rngNext
     in (GenRng $ XorShift.initialize newSeed1 newSeed2, GenRng rngNext')

-- | Generator monad
newtype Gen a = Gen { runGen :: GenRng -> GenParams -> a }

instance Functor Gen where
    fmap f g = Gen (\rng params -> f (runGen g rng params))

instance Applicative Gen where
    pure a     = Gen (\_ _ -> a)
    fab <*> fa = Gen $ \rng params ->
        let (r1,r2) = genGenerator rng
            ab      = runGen fab r1 params
            a       = runGen fa r2 params
         in ab a

instance Monad Gen where
    return a  = Gen (\_ _ -> a)
    ma >>= mb = Gen $ \rng params ->
            let (r1,r2) = genGenerator rng
                a       = runGen ma r1 params
             in runGen (mb a) r2 params

genWithRng :: forall a . (forall randomly . MonadRandom randomly => randomly a) -> Gen a
genWithRng f = Gen $ \(GenRng rng) _ ->
    let (a, _) = withRandomGenerator rng f in a

genWithParams :: (GenParams -> Gen a) -> Gen a
genWithParams f = Gen $ \rng params -> runGen (f params) rng params
