{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Common functions for property testing of PIR passes.
module PlutusIR.Properties.Common where
import PlutusCore.Builtin
import PlutusCore.Default
import Test.QuickCheck

instance Arbitrary (BuiltinSemanticsVariant DefaultFun) where
    arbitrary = elements [DefaultFunSemanticsVariant1, DefaultFunSemanticsVariant2]
