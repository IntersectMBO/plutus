{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}
module Flat.Spec (test_flat) where

import Data.Word
import Flat
import PlutusCore.DeBruijn
import Test.Tasty
import Test.Tasty.QuickCheck
import UntypedPlutusCore ()
import UntypedPlutusCore.Core.Type

test_deBruijnIso :: TestTree
test_deBruijnIso = testProperty "deBruijnIso" $ \d ->
    d === fromFake (toFake d)

test_fakeIso :: TestTree
test_fakeIso = testProperty "fakeIso" $ \fnd ->
    fnd === toFake (fromFake fnd)

test_deBruijnTripping :: TestTree
test_deBruijnTripping = testProperty "debruijnTripping" $ \d ->
    Right d === unflat (flat @DeBruijn d)

test_fakeTripping :: TestTree
test_fakeTripping = testProperty "fakeTripping" $ \fnd ->
    Right fnd === unflat (flat @FakeNamedDeBruijn fnd)

test_binderDeBruijn :: TestTree
test_binderDeBruijn = testProperty "binderDeBruijn" $ \b ->
    -- binders should always decode as init binder
    Right initB === unflat (flat @(Binder DeBruijn) b)

test_binderFake :: TestTree
test_binderFake = testProperty "binderFake" $ \bf ->
    -- binders should always decode as init binder
    Right (toFake <$> initB) === unflat (flat @(Binder FakeNamedDeBruijn) bf)

test_flat :: TestTree
test_flat = testGroup "FlatProp"
    [ test_deBruijnIso
    , test_fakeIso
    , test_deBruijnTripping
    , test_fakeTripping
    , test_binderDeBruijn
    , test_binderFake
    ]

-- Helpers

initB :: Binder DeBruijn
initB = Binder $ DeBruijn deBruijnInitIndex

-- orphans for QuickCheck generation
deriving via Word64 instance Arbitrary DeBruijn
instance Arbitrary FakeNamedDeBruijn where
    arbitrary= toFake <$> arbitrary -- via debruijn
deriving newtype instance Arbitrary (Binder DeBruijn)
deriving newtype instance Arbitrary (Binder FakeNamedDeBruijn)

