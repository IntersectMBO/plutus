{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.PIR.Builtin where

import Data.ByteString (ByteString)
import Data.Coerce
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Test.QuickCheck

import PlutusCore.Data

instance Arbitrary Data where
    arbitrary = error "implement me"
    shrink = error "implement me"

class ArbitraryBuiltin a where
    arbitraryBuiltin :: Gen a
    default arbitraryBuiltin :: Arbitrary a => Gen a
    arbitraryBuiltin = arbitrary

    shrinkBuiltin :: a -> [a]
    default shrinkBuiltin :: Arbitrary a => a -> [a]
    shrinkBuiltin = shrink

instance ArbitraryBuiltin ()
instance ArbitraryBuiltin Bool
instance ArbitraryBuiltin Integer
instance ArbitraryBuiltin Data

instance ArbitraryBuiltin Text where
    arbitraryBuiltin = Text.pack . getPrintableString <$> arbitrary
    shrinkBuiltin = map (Text.pack . getPrintableString) . shrink . PrintableString . Text.unpack

instance ArbitraryBuiltin ByteString where
    arbitraryBuiltin = Text.encodeUtf8 <$> arbitraryBuiltin
    shrinkBuiltin = map Text.encodeUtf8 . shrinkBuiltin . Text.decodeUtf8

newtype AsArbitraryBuiltin a = AsArbitraryBuiltin
    { unAsArbitraryBuiltin :: a
    }

instance ArbitraryBuiltin a => Arbitrary (AsArbitraryBuiltin a) where
    arbitrary = coerce $ arbitraryBuiltin @a
    shrink = coerce $ shrinkBuiltin @a

-- We could do this and the next one generically using 'ElaborateBuiltin', but it would be more
-- code, so we keep it simple.
instance ArbitraryBuiltin a => ArbitraryBuiltin [a] where
    arbitraryBuiltin = coerce $ arbitrary @[AsArbitraryBuiltin a]
    shrinkBuiltin = coerce $ shrink @[AsArbitraryBuiltin a]

instance (ArbitraryBuiltin a, ArbitraryBuiltin b) => ArbitraryBuiltin (a, b) where
    arbitraryBuiltin = coerce $ arbitrary @(AsArbitraryBuiltin a, AsArbitraryBuiltin b)
    shrinkBuiltin = coerce $ shrink @(AsArbitraryBuiltin a, AsArbitraryBuiltin b)
