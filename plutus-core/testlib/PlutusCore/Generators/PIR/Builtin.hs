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

-- | Same as 'Arbitrary' but specifically for Plutus built-in types, so that we are not tied to
-- the default implementation of the methods for a built-in type.
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

-- | For providing an 'Arbitrary' instance deferring to 'ArbitraryBuiltin'. Useful for implementing
-- 'ArbitraryBuiltin' for a polymorphic built-in type by taking the logic for handling spines from
-- the 'Arbitrary' class and the logic for handling elements from 'ArbitraryBuiltin'.
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
