{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeApplications #-}

module PlutusLedgerApi.Test.Orphans.V3.MintValue () where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Coerce (coerce)
import Data.Set qualified as Set
import PlutusLedgerApi.Test.Orphans.PlutusTx (getBlake2b244Hash)
import PlutusLedgerApi.Test.Orphans.V1.Value ()
import PlutusLedgerApi.V1.Value (CurrencySymbol (CurrencySymbol), TokenName (TokenName),
                                 Value (getValue))
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V3.MintValue (MintValue (UnsafeMintValue))
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude (toBuiltin)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), Arbitrary1 (liftArbitrary, liftShrink),
                        CoArbitrary, Function (function), Gen, NonZero (NonZero),
                        chooseBoundedIntegral, chooseInt, functionMap, getNonEmpty, getNonZero,
                        resize, scale, sized, vectorOf)

instance Arbitrary MintValue where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    UnsafeMintValue <$> do
      -- Generate a set of currency symbols that aren't Ada
      keySet <- Set.fromList
        <$> liftArbitrary (CurrencySymbol . getBlake2b244Hash <$> arbitrary)
      let keyList = Set.toList keySet
      -- For each key, generate a set of token name keys that aren't Ada
      keyVals <- traverse (scale (`quot` 8) . mkInner) keyList
      pure
        . getValue
        . foldMap (\(cs, vals) -> foldMap (uncurry (Value.singleton cs)) vals)
        $ keyVals
    where
      mkInner :: CurrencySymbol -> Gen (CurrencySymbol, [(TokenName, Integer)])
      mkInner cs =
        (cs,)
          . Set.toList
          . Set.fromList
          . getNonEmpty
          <$> liftArbitrary ((,) <$> genNonAdaTokenName <*> (getNonZero <$> arbitrary))

      genNonAdaTokenName :: Gen TokenName
      genNonAdaTokenName =
          fmap (TokenName . toBuiltin @ByteString . BS.pack) . sized $ \size -> do
            len <- resize size . chooseInt $ (1, 32)
            vectorOf len . chooseBoundedIntegral $ (33, 126)

  {-# INLINEABLE shrink #-}
  shrink (UnsafeMintValue v) =
    UnsafeMintValue <$> do
      -- To ensure we don't break anything, we shrink in only two ways:
      --
      -- 1. Dropping keys (outer or inner)
      -- 2. Shrinking amounts
      --
      -- To make this a bit easier on ourselves, we first 'unpack' the Value
      -- completely, shrink the resulting (nested) list, then 'repack'. As neither
      -- of these changes affect order or uniqueness, we're safe.
      let asList = fmap AssocMap.toList <$> AssocMap.toList v
      shrunk <- liftShrink
        (\(cs, inner) ->
           (cs,) <$> liftShrink
           (\(tn, amount) -> (tn,) . getNonZero <$> shrink (NonZero amount))
           inner) asList
      pure . AssocMap.unsafeFromList . fmap (fmap AssocMap.unsafeFromList) $ shrunk

deriving via Value instance CoArbitrary MintValue

instance Function MintValue where
  {-# INLINEABLE function #-}
  function = functionMap coerce UnsafeMintValue
