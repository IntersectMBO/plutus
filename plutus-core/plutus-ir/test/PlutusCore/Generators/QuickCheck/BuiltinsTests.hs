module PlutusCore.Generators.QuickCheck.BuiltinsTests where

import PlutusCore.Data
import PlutusCore.Generators.QuickCheck ()

import Codec.Serialise
import Test.QuickCheck

-- | This mainly tests that the `Data` generator isn't non-terminating or too slow.
prop_genData :: Property
prop_genData = withMaxSuccess 800 $ \(d :: Data) -> d === deserialise (serialise d)
