{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RoleAnnotations  #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.PlutusTx (
  Blake2b256Hash (..),
  Blake2b244Hash (..),
  getBlake2b256Hash,
  getBlake2b244Hash,
  ) where

import Data.ByteString (ByteString)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Set qualified as Set
import PlutusLedgerApi.Test.Common.QuickCheck.Utils (unSizedByteString)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Prelude qualified as PlutusTx
import Test.QuickCheck (Arbitrary (arbitrary, shrink), Arbitrary1 (liftArbitrary, liftShrink),
                        CoArbitrary (coarbitrary), Function (function), Gen,
                        NonNegative (NonNegative), functionMap, getNonNegative, liftArbitrary,
                        oneof, scale, sized, variant)
import Test.QuickCheck.Instances.ByteString ()

instance Arbitrary PlutusTx.BuiltinByteString where
  {-# INLINEABLE arbitrary #-}
  arbitrary = PlutusTx.toBuiltin @ByteString <$> arbitrary
  {-# INLINEABLE shrink #-}
  shrink = fmap (PlutusTx.toBuiltin @ByteString) . shrink . PlutusTx.fromBuiltin

instance CoArbitrary PlutusTx.BuiltinByteString where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = coarbitrary . PlutusTx.fromBuiltin

instance Function PlutusTx.BuiltinByteString where
  {-# INLINEABLE function #-}
  function = functionMap PlutusTx.fromBuiltin (PlutusTx.toBuiltin @ByteString)

{- | Wrapper for BLAKE2b-244 hashes for convenience.
-}
newtype Blake2b244Hash = Blake2b244Hash PlutusTx.BuiltinByteString
  deriving (Eq, Ord) via PlutusTx.BuiltinByteString
  deriving stock (Show)

-- No shrinker, as it doesn't make much sense to.
instance Arbitrary Blake2b244Hash where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    Blake2b244Hash . PlutusTx.toBuiltin @ByteString . unSizedByteString @28 <$> arbitrary

deriving via PlutusTx.BuiltinByteString instance CoArbitrary Blake2b244Hash

getBlake2b244Hash :: Blake2b244Hash -> PlutusTx.BuiltinByteString
getBlake2b244Hash = coerce

-- Wrapper for BLAKE2b-256 hashes for convenience.
newtype Blake2b256Hash = Blake2b256Hash PlutusTx.BuiltinByteString
  deriving (Eq, Ord) via PlutusTx.BuiltinByteString
  deriving stock (Show)

-- No shrinker, as it doesn't make much sense to.
instance Arbitrary Blake2b256Hash where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    Blake2b256Hash . PlutusTx.toBuiltin @ByteString . unSizedByteString @32 <$> arbitrary

deriving via PlutusTx.BuiltinByteString instance CoArbitrary Blake2b256Hash

getBlake2b256Hash :: Blake2b256Hash -> PlutusTx.BuiltinByteString
getBlake2b256Hash = coerce

{- | This is a very general instance, able to produce 'PlutusTx.BuiltinData' of
basically any shape. You probably want something more focused than this.
-}
instance Arbitrary PlutusTx.BuiltinData where
  {-# INLINEABLE arbitrary #-}
  arbitrary = sized $ \size -> go size
    where
      scaleDown :: forall (a :: Type). Gen a -> Gen a
      scaleDown = scale (`quot` 4)
      go :: Int -> Gen PlutusTx.BuiltinData
      go size
        | size <= 0 = oneof [genB, genI]
        | otherwise = oneof [genB, genI, genConstr, genList, genMap]
      genB :: Gen PlutusTx.BuiltinData
      genB = Builtins.mkB <$> arbitrary
      genI :: Gen PlutusTx.BuiltinData
      genI = Builtins.mkI <$> arbitrary
      genConstr :: Gen PlutusTx.BuiltinData
      genConstr =
        Builtins.mkConstr . getNonNegative
          <$> arbitrary
          <*> scaleDown (liftArbitrary arbitrary)
      genList :: Gen PlutusTx.BuiltinData
      genList =
        Builtins.mkList <$> scaleDown (liftArbitrary arbitrary)
      genMap :: Gen PlutusTx.BuiltinData
      genMap =
        Builtins.mkMap <$> scaleDown (liftArbitrary ((,) <$> arbitrary <*> arbitrary))
  {-# INLINEABLE shrink #-}
  shrink dat =
    Builtins.matchData
      dat
      shrinkConstr
      shrinkMap
      shrinkList
      (fmap (Builtins.mkI . getNonNegative) . shrink . NonNegative)
      (fmap Builtins.mkB . shrink)
    where
      shrinkConstr :: Integer -> [PlutusTx.BuiltinData] -> [PlutusTx.BuiltinData]
      shrinkConstr ix dats = do
        NonNegative ix' <- shrink (NonNegative ix)
        dats' <- shrink dats
        pure . Builtins.mkConstr ix' $ dats'
      shrinkMap :: [(PlutusTx.BuiltinData, PlutusTx.BuiltinData)] -> [PlutusTx.BuiltinData]
      shrinkMap kvs = Builtins.mkMap <$> shrink kvs
      shrinkList :: [PlutusTx.BuiltinData] -> [PlutusTx.BuiltinData]
      shrinkList ell = Builtins.mkList <$> shrink ell

instance CoArbitrary PlutusTx.BuiltinData where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary dat =
    Builtins.matchData
      dat
      (\ix dats -> variant (0 :: Int) . coarbitrary ix . coarbitrary dats)
      (\kvs -> variant (1 :: Int) . coarbitrary kvs)
      (\ell -> variant (2 :: Int) . coarbitrary ell)
      (\i -> variant (3 :: Int) . coarbitrary i)
      (\bs -> variant (4 :: Int) . coarbitrary bs)

instance Function PlutusTx.BuiltinData where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        PlutusTx.BuiltinData ->
        Either
          (Integer, [PlutusTx.BuiltinData])
          ( Either
              [(PlutusTx.BuiltinData, PlutusTx.BuiltinData)]
              ( Either
                  [PlutusTx.BuiltinData]
                  ( Either Integer PlutusTx.BuiltinByteString
                  )
              )
          )
      into dat =
        Builtins.matchData
          dat
          (\ix -> Left . (ix,))
          (Right . Left)
          (Right . Right . Left)
          (Right . Right . Right . Left)
          (Right . Right . Right . Right)
      outOf ::
        Either
          (Integer, [PlutusTx.BuiltinData])
          ( Either
              [(PlutusTx.BuiltinData, PlutusTx.BuiltinData)]
              ( Either
                  [PlutusTx.BuiltinData]
                  ( Either Integer PlutusTx.BuiltinByteString
                  )
              )
          ) ->
        PlutusTx.BuiltinData
      outOf = \case
        Left (ix, dats) -> Builtins.mkConstr ix dats
        Right (Left kvs) -> Builtins.mkMap kvs
        Right (Right (Left ell)) -> Builtins.mkList ell
        Right (Right (Right (Left i))) -> Builtins.mkI i
        Right (Right (Right (Right bs))) -> Builtins.mkB bs

{- | This generates well-defined maps: specifically, there are no duplicate
keys. To ensure that this is preserved, we do not shrink keys: we only drop
whole entries, or shrink values associated with keys.

In order to make this instance even moderately efficient, we require an 'Ord'
constraint on keys. In practice, this isn't a significant limitation, as
basically all Plutus types have such an instance.

-}
instance (Arbitrary k, Ord k) => Arbitrary1 (AssocMap.Map k) where
  {-# INLINEABLE liftArbitrary #-}
  liftArbitrary genVal =
    AssocMap.unsafeFromList <$> do
      -- First, generate a Set of keys to ensure no duplication
      keyList <- Set.toList <$> arbitrary
      -- Then generate a value for each
      traverse (\key -> (key,) <$> genVal) keyList
  {-# INLINEABLE liftShrink #-}
  liftShrink shrinkVal aMap =
    AssocMap.unsafeFromList <$> do
      let asList = AssocMap.toList aMap
      liftShrink (\(key, val) -> (key,) <$> shrinkVal val) asList

instance (Arbitrary k, Arbitrary v, Ord k) => Arbitrary (AssocMap.Map k v) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = liftArbitrary arbitrary
  {-# INLINEABLE shrink #-}
  shrink = liftShrink shrink

instance (CoArbitrary k, CoArbitrary v) => CoArbitrary (AssocMap.Map k v) where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = coarbitrary . AssocMap.toList

instance (Function k, Function v) => Function (AssocMap.Map k v) where
  {-# INLINEABLE function #-}
  function = functionMap AssocMap.toList AssocMap.unsafeFromList
