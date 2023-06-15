-- editorconfig-checker-disable-file
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
module Flat.Spec (test_flat) where

import Data.Word
import Flat
import PlutusCore.DeBruijn
import Test.Tasty
import Test.Tasty.QuickCheck
import UntypedPlutusCore ()
import UntypedPlutusCore.Core.Type

test_flat :: TestTree
test_flat = testGroup "FlatProp"
    [ test_iso
    , test_deBruijnTripping
    , test_binderDecode
    ]

deriving via Word64 instance Arbitrary DeBruijn
instance Arbitrary FakeNamedDeBruijn where
    arbitrary= toFake <$> arbitrary -- via debruijn
deriving newtype instance Arbitrary (Binder DeBruijn)
deriving newtype instance Arbitrary (Binder FakeNamedDeBruijn)

test_iso :: TestTree
test_iso = testProperty "fakeIso" $ \d fnd ->
         (d === fromFake (toFake d))
    .&&. (fnd === toFake (fromFake fnd))

test_deBruijnTripping :: TestTree
test_deBruijnTripping = testProperty "debruijnTripping" $ \(d :: DeBruijn) (f :: FakeNamedDeBruijn) ->
      Right d === (unflat $ flat d)
  .&&. Right f === (unflat $ flat f)

test_binderDecode :: TestTree
test_binderDecode = testProperty "binder" $ \(b :: Binder DeBruijn) (bf :: Binder FakeNamedDeBruijn) ->
   -- binders should always decode as init binder
   Right initB === (unflat $ flat b)
 .&&. Right (toFake <$> initB) === (unflat $ flat bf)
  where
     initB = Binder $ DeBruijn deBruijnInitIndex
