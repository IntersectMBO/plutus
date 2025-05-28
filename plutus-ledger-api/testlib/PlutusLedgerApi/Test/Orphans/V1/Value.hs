{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusLedgerApi.Test.Orphans.V1.Value (
  -- * Specialized Value wrappers
  FeeValue (..),
  getFeeValue,
  UTxOValue (..),
  getUtxoValue,
  ZeroAdaValue (..),
  getZeroAdaValue,
  MintValue (..),
  getMintValue,
) where

import Control.Monad (guard)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Coerce (coerce)
import Data.Set qualified as Set
import PlutusLedgerApi.Test.Orphans.PlutusTx (getBlake2b244Hash)
import PlutusLedgerApi.V1.Value (AssetClass (AssetClass), CurrencySymbol (CurrencySymbol),
                                 Lovelace (Lovelace), TokenName (TokenName), Value (Value),
                                 adaSymbol, adaToken, getValue, singleton, valueOf)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Prelude qualified as PlutusTx
import Test.QuickCheck (Arbitrary (arbitrary, shrink), Arbitrary1 (liftArbitrary, liftShrink),
                        CoArbitrary, Function (function), Gen, Large (getLarge),
                        NonEmptyList (NonEmpty), NonZero (NonZero), Positive (Positive),
                        chooseBoundedIntegral, chooseInt, frequency, functionMap, getNonEmpty,
                        getNonZero, getPositive, resize, scale, sized, vectorOf)

deriving via (CurrencySymbol, TokenName) instance Arbitrary AssetClass

deriving via (CurrencySymbol, TokenName) instance CoArbitrary AssetClass

instance Function AssetClass where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into :: AssetClass -> (CurrencySymbol, TokenName)
      into = coerce

      outOf :: (CurrencySymbol, TokenName) -> AssetClass
      outOf = coerce


deriving via Integer instance Arbitrary Lovelace

deriving via Integer instance CoArbitrary Lovelace

instance Function Lovelace where
  {-# INLINEABLE function #-}
  function = functionMap coerce Lovelace


{- | A 'CurrencySymbol' is either a BLAKE2b-244 hash or empty (representing the
Ada symbol). In a fully-fair generator, this makes it vanishingly unlikely
that the Ada symbol will be produced naturally (1 in 2^8^28 = 2^244) odds.
QuickCheck doesn't give us the ability to represent these odds faithfully:
thus, we merely make the Ada symbol as unlikely as we can. If you want to
ensure that the Ada symbol is covered by your tests, you need to make
dedicated tests for this. For this reason, we also don't shrink into the Ada
symbol (indeed, we don't shrink at all).
-}
instance Arbitrary CurrencySymbol where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    CurrencySymbol
      <$> frequency
        [ (1, pure "")
        , (maxBound, getBlake2b244Hash <$> arbitrary)
        ]

deriving via PlutusTx.BuiltinByteString instance CoArbitrary CurrencySymbol

instance Function CurrencySymbol where
  {-# INLINEABLE function #-}
  function = functionMap coerce CurrencySymbol


{- | A 'Value' suitable for 'TxOut'. Specifically:

* The `Value` is sorted by both keys (meaning 'CurrencySymbol' and
  'TokenName');
* There exists an Ada amount; and
* All amounts are positive.

= Note

This is designed to act as a modifier, and thus, we expose the constructor
even though it preserves invariants. If you use the constructor directly,
be /very/ certain that the Value being wrapped satisfies the invariants
described above: failing to do so means all guarantees of this type are off
the table.
-}
newtype UTxOValue = UTxOValue Value
  deriving (Eq) via Value
  deriving stock (Show)

instance Arbitrary UTxOValue where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    UTxOValue <$> do
      Positive adaQuantity <- arbitrary
      -- Set of non-Ada currency symbols
      csSet <- Set.fromList <$> liftArbitrary (CurrencySymbol . getBlake2b244Hash <$> arbitrary)
      let cses = Set.toList csSet
      -- For each key, generate a set of token names that aren't Ada, and a
      -- positive value
      table <- traverse (scale (`quot` 8) . mkInner) cses
      -- Jam the Ada value in there
      let table' = (adaSymbol, [(adaToken, adaQuantity)]) : table
      pure . Value . AssocMap.unsafeFromList . fmap (fmap AssocMap.unsafeFromList) $ table'
    where
      mkInner :: CurrencySymbol -> Gen (CurrencySymbol, [(TokenName, Integer)])
      mkInner cs =
        (cs,) <$> do
          -- Set of non-Ada token names
          tnSet <- Set.fromList <$> liftArbitrary genNonAdaTokenName
          let asList = Set.toList tnSet
          traverse (\tn -> (tn,) . getPositive <$> arbitrary) asList

      genNonAdaTokenName :: Gen TokenName
      genNonAdaTokenName =
        TokenName . PlutusTx.toBuiltin @ByteString . BS.pack <$> do
          len <- chooseInt (1, 32)
          -- ASCII printable range
          vectorOf len . chooseBoundedIntegral $ (33, 126)

  {-# INLINEABLE shrink #-}
  shrink (UTxOValue (Value v)) =
    UTxOValue . Value <$> do
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
            (\(tn, amount) -> (tn,) . getPositive <$> shrink (Positive amount))
            inner) asList
      pure . AssocMap.unsafeFromList . fmap (fmap AssocMap.unsafeFromList) $ shrunk

deriving via Value instance CoArbitrary UTxOValue

instance Function UTxOValue where
  {-# INLINEABLE function #-}
  function = functionMap coerce UTxOValue

getUtxoValue :: UTxOValue -> Value
getUtxoValue = coerce

{- | A 'Value' that contains zero Ada.

= Note

This is designed to act as a modifier, and thus, we expose the constructor
even though it preserves invariants. If you use the constructor directly,
be /very/ certain that the Value being wrapped satisfies the invariants
described above: failing to do so means all guarantees of this type are off
the table.
-}
newtype ZeroAdaValue = ZeroAdaValue Value
  deriving (Eq) via Value
  deriving stock (Show)

instance Arbitrary ZeroAdaValue where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    ZeroAdaValue <$> do
      -- Generate a set of currency symbols that aren't Ada
      keySet <- fmap
                  Set.fromList
                  (liftArbitrary (CurrencySymbol . getBlake2b244Hash <$> arbitrary))
      let keyList = Set.toList keySet
      -- For each key, generate a set of token name keys that aren't Ada
      keyVals <- traverse (scale (`quot` 8) . mkInner) keyList
      pure
        . withZeroAda
        . foldMap (\(cs, vals) -> foldMap (uncurry (singleton cs)) vals)
        $ keyVals
    where
      mkInner :: CurrencySymbol -> Gen (CurrencySymbol, [(TokenName, Integer)])
      mkInner cs =
        (cs,)
          . Set.toList
          . Set.fromList
          . getNonEmpty <$> liftArbitrary ((,) <$> genNonAdaTokenName <*> arbitrary)

      genNonAdaTokenName :: Gen TokenName
      genNonAdaTokenName =
          fmap (TokenName . PlutusTx.toBuiltin @ByteString . BS.pack) . sized $ \size -> do
            len <- resize size . chooseInt $ (1, 32)
            vectorOf len . chooseBoundedIntegral $ (33, 126)

  {-# INLINEABLE shrink #-}
  -- Since we can't shrink keys anyway, we just borrow the stock shrinker
  shrink (ZeroAdaValue v) = ZeroAdaValue . withZeroAda <$> shrink v

deriving via Value instance CoArbitrary ZeroAdaValue

instance Function ZeroAdaValue where
  {-# INLINEABLE function #-}
  function = functionMap coerce ZeroAdaValue

getZeroAdaValue :: ZeroAdaValue -> Value
getZeroAdaValue = coerce


{- | This is the most general possible instance for 'Value'. In particular,
this can have zero values, and does not treat the Ada symbol or token name
specially.
-}
instance Arbitrary Value where
  {-# INLINEABLE arbitrary #-}
  arbitrary = Value <$> liftArbitrary (scale (`quot` 4) arbitrary)
  {-# INLINEABLE shrink #-}
  shrink = fmap Value . shrink . getValue

deriving via
  (AssocMap.Map CurrencySymbol (AssocMap.Map TokenName Integer))
  instance
    CoArbitrary Value

instance Function Value where
  {-# INLINEABLE function #-}
  function = functionMap coerce Value


{- | This instance can generate the Ada token name, with faithful odds. It is
limited to generating printable ASCII names, rather than the full UTF-8
range. We did this for two reasons:

1. For testing purposes, we should prioritize readability, hence our choice
   of a textual representation; and
2. It is difficult to work within the size limit (32 bytes) when generating
   UTF-8.
-}
instance Arbitrary TokenName where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    fmap (TokenName . PlutusTx.toBuiltin @ByteString . BS.pack) . sized $ \size -> do
      -- We want the length to be size-dependent
      len <- resize size . chooseInt $ (0, 32)
      -- But the bytes themselves should not be: the whole ASCII printable range
      -- should be available always
      vectorOf len . chooseBoundedIntegral $ (33, 126)

  {-# INLINEABLE shrink #-}
  shrink tn =
    TokenName . PlutusTx.toBuiltin @ByteString <$> do
      let asList = BS.unpack . PlutusTx.fromBuiltin @PlutusTx.BuiltinByteString . coerce $ tn
      bs <- BS.pack <$> shrink asList
      guard (BS.all (\w8 -> w8 >= 33 && w8 <= 126) bs)
      pure bs

deriving via PlutusTx.BuiltinByteString instance CoArbitrary TokenName

instance Function TokenName where
  {-# INLINEABLE function #-}
  function = functionMap coerce TokenName

-- Helpers

-- This is frankly a bizarre omission
instance Arbitrary1 NonEmptyList where
  {-# INLINEABLE liftArbitrary #-}
  liftArbitrary genInner =
    NonEmpty <$> do
      x <- genInner
      xs <- liftArbitrary genInner
      pure $ x : xs

  {-# INLINEABLE liftShrink #-}
  liftShrink shrinkInner (NonEmpty ell) =
    NonEmpty <$> case ell of
      []       -> []
      (x : xs) -> (:) <$> shrinkInner x <*> liftShrink shrinkInner xs

{- | A 'Value' containing only Ada, suitable for fees. Furthermore, the
Ada quantity is positive.

= Note

This is designed to act as a modifier, and thus, we expose the constructor
even though it preserves invariants. If you use the constructor directly,
be /very/ certain that the Value being wrapped satisfies the invariants
described above: failing to do so means all guarantees of this type are off
the table.
-}
newtype FeeValue = FeeValue Value
  deriving (Eq) via Value
  deriving stock (Show)

instance Arbitrary FeeValue where
  {-# INLINEABLE arbitrary #-}
  arbitrary = FeeValue
    . singleton adaSymbol adaToken
    . fromIntegral @Int
    . getLarge
    . getPositive
    <$> arbitrary

  {-# INLINEABLE shrink #-}
  shrink (FeeValue v) =
    FeeValue . singleton adaSymbol adaToken <$> do
      let adaAmount = valueOf v adaSymbol adaToken
      Positive adaAmount' <- shrink (Positive adaAmount)
      pure adaAmount'

deriving via Value instance CoArbitrary FeeValue

instance Function FeeValue where
  {-# INLINEABLE function #-}
  function = functionMap coerce FeeValue

getFeeValue :: FeeValue -> Value
getFeeValue = coerce


{- | Similar to 'ZeroAdaValue', but also does not have nonzero amounts.

= Note

This is designed to act as a modifier, and thus, we expose the constructor
even though it preserves invariants. If you use the constructor directly,
be /very/ certain that the Value being wrapped satisfies the invariants
described above: failing to do so means all guarantees of this type are off
the table.
-}
newtype MintValue = MintValue Value
  deriving (Eq) via Value
  deriving stock (Show)

instance Arbitrary MintValue where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    MintValue <$> do
      -- Generate a set of currency symbols that aren't Ada
      keySet <- fmap
                Set.fromList
                (liftArbitrary (CurrencySymbol . getBlake2b244Hash <$> arbitrary))
      let keyList = Set.toList keySet
      -- For each key, generate a set of token name keys that aren't Ada
      keyVals <- traverse (scale (`quot` 8) . mkInner) keyList
      pure
        . withZeroAda
        . foldMap (\(cs, vals) -> foldMap (uncurry (singleton cs)) vals)
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
          fmap (TokenName . PlutusTx.toBuiltin @ByteString . BS.pack) . sized $ \size -> do
            len <- resize size . chooseInt $ (1, 32)
            vectorOf len . chooseBoundedIntegral $ (33, 126)

  {-# INLINEABLE shrink #-}
  shrink (MintValue (Value v)) =
    MintValue . withZeroAda . Value <$> do
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
  function = functionMap coerce MintValue

getMintValue :: MintValue -> Value
getMintValue = coerce

withZeroAda :: Value -> Value
withZeroAda = (singleton adaSymbol adaToken 0 <>)
