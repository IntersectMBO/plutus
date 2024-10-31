{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RoleAnnotations  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module PlutusLedgerApi.Test.Common.QuickCheck.Utils (
  SizedByteString (SizedByteString),
  unSizedByteString,
  AsWord64 (AsWord64),
  fromAsWord64,
) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Coerce (coerce)
import Data.Proxy (Proxy (Proxy))
import Data.Word (Word64)
import GHC.TypeNats (KnownNat, Natural, natVal)
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary, Function (function),
                        functionMap, vectorOf)
import Test.QuickCheck.Instances.ByteString ()

{- | Helper for 'ByteString's of a fixed length. We don't expose the
constructor, instead providing a read-only pattern, as well as an accessor
function, to ensure that the size invariant is maintained.
-}
newtype SizedByteString (n :: Natural) = UnsafeSizedByteString ByteString
  deriving
    (Eq
    ,Ord
    )
    via ByteString
  deriving stock
    (Show
    )

type role SizedByteString nominal

instance KnownNat n => Arbitrary (SizedByteString n) where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    UnsafeSizedByteString . BS.pack <$> do
      let !len = fromIntegral . natVal $ Proxy @n
      vectorOf len arbitrary
  {-# INLINEABLE shrink #-}
  shrink =
    fmap (UnsafeSizedByteString . BS.pack)
      . traverse shrink
      . BS.unpack
      . unSizedByteString

deriving via ByteString instance CoArbitrary (SizedByteString n)


instance Function (SizedByteString n) where
  {-# INLINEABLE function #-}
  function = functionMap coerce UnsafeSizedByteString

{- | Read-only pattern for accessing the underlying 'ByteString'. Use it just
like you would use a data constructor in a pattern match.
-}
pattern SizedByteString :: forall (n :: Natural). ByteString -> SizedByteString n
pattern SizedByteString bs <- UnsafeSizedByteString bs

{-# COMPLETE SizedByteString #-}

{- | Get the underlying 'ByteString'. It is guaranteed to have the length
specified in its type.
-}
unSizedByteString ::
  forall (n :: Natural).
  SizedByteString n ->
  ByteString
unSizedByteString = coerce

{- | Plutus' ledger API often has to \'fake\' 'Word64' using the much larger
'Integer' type. This helper is designed to generate 'Integer's that fit into
'Word64'.

We don't expose the constructor directly; instead, we provide a read-only
pattern and an accessor function.
-}
newtype AsWord64 = UnsafeAsWord64 Word64
  deriving
    (Eq
    ,Ord
    ,Arbitrary
    ,CoArbitrary
    )
    via Word64
  deriving stock
    (Show
    )

instance Function AsWord64 where
  {-# INLINEABLE function #-}
  function = functionMap coerce UnsafeAsWord64

{- | Read-only pattern for accessing the underlying 'Integer'. Use it just like
you would use a data constructor in a pattern match.
-}
pattern AsWord64 :: Integer -> AsWord64
pattern AsWord64 i <- (fromAsWord64 -> i)

fromAsWord64 :: AsWord64 -> Integer
fromAsWord64 = fromIntegral . coerce @_ @Word64
