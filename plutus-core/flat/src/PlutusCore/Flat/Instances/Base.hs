{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Flat instances for the base library
module PlutusCore.Flat.Instances.Base () where

import Control.Monad (liftM2)
import Data.Bool
import Data.Char
import Data.Complex (Complex (..))
import Data.Fixed
-- #if MIN_VERSION_base(4,9,0)
import Data.List.NonEmpty qualified as B
-- #endif

#if ! MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Monoid (mempty)
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup qualified as Semigroup
#endif

import Data.Monoid qualified as Monoid
import Data.Ratio
import PlutusCore.Flat.Instances.Util
import Prelude hiding (mempty)

-- #if !MIN_VERSION_base(4,9,0)
-- import           Data.Monoid           ((<>))
-- #endif

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Identity (Identity (..))
#endif

-- #if !MIN_VERSION_base(4,9,0)
-- deriving instance Generic (Complex a)
-- #endif

{- ORMOLU_DISABLE -}
-- $setup
-- >>> :set -XNegativeLiterals -XTypeApplications
-- >>> import PlutusCore.Flat.Instances.Test
-- >>> import Data.Fixed
-- >>> import Data.Int
-- >>> import Data.Complex(Complex(..))
-- >>> import Numeric.Natural
-- >>> import Data.Word
-- >>> import Data.Ratio
-- >>> import PlutusCore.Flat.Run
-- >>> import Data.Monoid
-- >>> import qualified Data.List.NonEmpty as B
-- >>> let test = tstBits
-- >>> let y = 33
{- ORMOLU_ENABLE -}

-- >>> y

-- | @since 0.4.4
#if MIN_VERSION_base(4,8,0)
instance Flat Monoid.All where
    encode (Monoid.All a) = encode a
    size (Monoid.All a) = size a
    decode = Monoid.All <$> decode

{- |

>>> let w = Just (11::Word8); a = Alt w <> Alt (Just 24) in tst a == tst w
True

>>> let w = Just (11::Word8); a = Alt Nothing <> Alt w in tst a == tst w
True

@since 0.4.4
-}
instance Flat (f a) => Flat (Monoid.Alt f a) where
    encode (Monoid.Alt a) = encode a
    size (Monoid.Alt a) = size a
    decode = Monoid.Alt <$> decode
#endif

#if MIN_VERSION_base(4,9,0)
-- | @since 0.4.4
instance Flat a => Flat (Identity a) where
    encode (Identity a) = encode a
    size (Identity a) = size a
    decode = Identity <$> decode
#endif

-- | @since 0.4.4
instance Flat a => Flat (Monoid.Dual a) where
    encode (Monoid.Dual a) = encode a
    size (Monoid.Dual a) = size a
    decode = Monoid.Dual <$> decode

-- | @since 0.4.4
instance Flat Monoid.Any where
    encode (Monoid.Any a) = encode a
    size (Monoid.Any a) = size a
    decode = Monoid.Any <$> decode

-- | @since 0.4.4
instance Flat a => Flat (Monoid.Sum a) where
    encode (Monoid.Sum a) = encode a
    size (Monoid.Sum a) = size a
    decode = Monoid.Sum <$> decode

-- | @since 0.4.4
instance Flat a => Flat (Monoid.Product a) where
    encode (Monoid.Product a) = encode a
    size (Monoid.Product a) = size a
    decode = Monoid.Product <$> decode

#if MIN_VERSION_base(4,9,0)
-- | @since 0.4.4
instance Flat a => Flat (Semigroup.Min a) where
    encode (Semigroup.Min a) = encode a
    size (Semigroup.Min a) = size a
    decode = Semigroup.Min <$> decode

-- | @since 0.4.4
instance Flat a => Flat (Semigroup.Max a) where
    encode (Semigroup.Max a) = encode a
    size (Semigroup.Max a) = size a
    decode = Semigroup.Max <$> decode

-- | @since 0.4.4
instance Flat a => Flat (Semigroup.First a) where
    encode (Semigroup.First a) = encode a
    size (Semigroup.First a) = size a
    decode = Semigroup.First <$> decode

-- | @since 0.4.4
instance Flat a => Flat (Semigroup.Last a) where
    encode (Semigroup.Last a) = encode a
    size (Semigroup.Last a) = size a
    decode = Semigroup.Last <$> decode
#endif

{- |
`()`, as all data types with a single constructor, has a zero-length encoding.

>>> test ()
(True,0,"")
-}
instance Flat () where
    encode _ = mempty

    size _ = id

    decode = pure ()

{- |
One bit is plenty for a Bool.

>>> test False
(True,1,"0")

>>> test True
(True,1,"1")
-}
instance Flat Bool where
    encode = eBool

    size = sBool

    decode = dBool

{- |
Char's are mapped to Word32 and then encoded.

For ascii characters, the encoding is standard ascii.

>>> test 'a'
(True,8,"01100001")

For unicode characters, the encoding is non standard.

>>> test 'È'
(True,16,"11001000 00000001")

>>> test '不'
(True,24,"10001101 10011100 00000001")

#ifndef ETA
>>> test "\x1F600"
(True,26,"11000000 01110110 00000011 10")
#endif
-}
instance Flat Char where
    size = sChar

    encode = eChar

    decode = dChar

{- |
>>> test (Nothing::Maybe Bool)
(True,1,"0")

>>> test (Just False::Maybe Bool)
(True,2,"10")
-}
instance Flat a => Flat (Maybe a)

{- |
>>> test (Left False::Either Bool ())
(True,2,"00")

>>> test (Right ()::Either Bool ())
(True,1,"1")
-}
instance (Flat a, Flat b) => Flat (Either a b)

{- |
>>> test (MkFixed 123 :: Fixed E0)
(True,16,"11110110 00000001")

>>> test (MkFixed 123 :: Fixed E0) == test (MkFixed 123 :: Fixed E2)
True
-}
instance Flat (Fixed a) where
    encode (MkFixed n) = encode n

    size (MkFixed n) = size n

    decode = MkFixed <$> decode

{- |
Word8 always take 8 bits.

>>> test (0::Word8)
(True,8,"00000000")

>>> test (255::Word8)
(True,8,"11111111")
-}
instance Flat Word8 where
    encode = eWord8

    decode = dWord8

    size = sWord8

{- |
Natural, Word, Word16, Word32 and Word64 are encoded as a non empty list of 7 bits chunks (least significant chunk first and most significant bit first in every chunk).

Words are always encoded in a whole number of bytes, as every chunk is 8 bits long (1 bit for the List constructor, plus 7 bits for the value).

The actual definition is:

@
Word64 ≡   Word64 Word

Word32 ≡   Word32 Word

Word16 ≡   Word16 Word

Word ≡   Word (LeastSignificantFirst (NonEmptyList (MostSignificantFirst Word7)))

LeastSignificantFirst a ≡   LeastSignificantFirst a

NonEmptyList a ≡   Elem a
                 | Cons a (NonEmptyList a)

MostSignificantFirst a ≡   MostSignificantFirst a

Word7 ≡   V0
        | V1
        | V2
        ...
        | V127
@

Values between as 0 and 127 fit in a single byte.

127 (0b1111111) is represented as Elem V127 and encoded as: Elem=0 127=1111111

>>> test (127::Word)
(True,8,"01111111")

254 (0b11111110) is represented as Cons V126 (Elem V1) (254=128+126) and encoded as: Cons=1 V126=1111110 (Elem=0 V1=0000001):

>>> test (254::Word)
(True,16,"11111110 00000001")

Another example, 32768 (Ob1000000000000000 = 0000010 0000000 0000000):

>>> test (32768::Word32)
(True,24,"10000000 10000000 00000010")

As this is a variable length encoding, values are encoded in the same way, whatever their type:

>>> all (test (3::Word) ==) [test (3::Word16),test (3::Word32),test (3::Word64)]
True


Word/Int decoders return an error if the encoded value is outside their valid range:

>>> unflat @Word16 (flat @Word32 $ fromIntegral @Word16 maxBound)
Right 65535

>>> unflat @Word16 (flat @Word32 $ fromIntegral @Word16 maxBound + 1)
Left (BadEncoding ...

>>> unflat @Word32 (flat @Word64 $ fromIntegral @Word32 maxBound)
Right 4294967295

>>> unflat @Word32 (flat @Word64 $ fromIntegral @Word32 maxBound + 1)
Left (BadEncoding ...

>>> unflat @Word64 (flat @Natural $ fromIntegral @Word64 maxBound)
Right 18446744073709551615

>>> unflat @Word64 (flat @Natural $ fromIntegral @Word64 maxBound + 1)
Left (BadEncoding ...



>>> unflat @Int16 (flat @Int32 $ fromIntegral @Int16 maxBound)
Right 32767

>>> unflat @Int16 (flat @Int32 $ fromIntegral @Int16 maxBound + 1)
Left (BadEncoding ...

>>> unflat @Int32 (flat @Int64 $ fromIntegral @Int32 maxBound)
Right 2147483647

>>> unflat @Int32 (flat @Int64 $ fromIntegral @Int32 maxBound + 1)
Left (BadEncoding ...

>>> unflat @Int64 (flat @Integer $ fromIntegral @Int64 maxBound)
Right 9223372036854775807

>>> unflat @Int64 (flat @Integer $ fromIntegral @Int64 maxBound + 1)
Left (BadEncoding ...


>>> unflat @Int16 (flat @Int32 $ fromIntegral @Int16 minBound)
Right (-32768)

>>> unflat @Int16 (flat @Int32 $ fromIntegral @Int16 minBound - 1)
Left (BadEncoding ...

>>> unflat @Int32 (flat @Int64 $ fromIntegral @Int32 minBound)
Right (-2147483648)

>>> unflat @Int32 (flat @Int64 $ fromIntegral @Int32 minBound - 1)
Left (BadEncoding ...

>>> unflat @Int64 (flat @Integer $ fromIntegral @Int64 minBound)
Right (-9223372036854775808)

>>> unflat @Int64 (flat @Integer $ fromIntegral @Int64 minBound - 1)
Left (BadEncoding ...
-}
instance Flat Word where
    size = sWord

    encode = eWord

    decode = dWord

{- |
Naturals are encoded just as the fixed size Words.

>>> test (0::Natural)
(True,8,"00000000")

>>> test (2^120::Natural)
(True,144,"10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 00000010")
-}
instance Flat Natural where
    size = sNatural

    encode = eNatural

    decode = dNatural

instance Flat Word16 where
    encode = eWord16

    decode = dWord16

    size = sWord16

instance Flat Word32 where
    encode = eWord32

    decode = dWord32

    size = sWord32

instance Flat Word64 where
    encode = eWord64

    decode = dWord64

    size = sWord64

{- |
Integer, Int, Int16, Int32 and Int64 are defined as the <https://developers.google.com/protocol-buffers/docs/encoding#signed-integers ZigZag> encoded version of the equivalent unsigned Word:

@
Int   ≡  Int   (ZigZag Word)

Int64 ≡  Int64 (ZigZag Word64)

Int32 ≡  Int32 (ZigZag Word32)

Int16 ≡  Int16 (ZigZag Word16)

Int8  ≡  Int8  (ZigZag Word8)

ZigZag a ≡ ZigZag a
@

ZigZag encoding alternates between positive and negative numbers, so that numbers whose absolute value is small can be encoded efficiently:

>>> test (0::Int)
(True,8,"00000000")

>>> test (-1::Int)
(True,8,"00000001")

>>> test (1::Int)
(True,8,"00000010")

>>> test (-2::Int)
(True,8,"00000011")

>>> test (2::Int)
(True,8,"00000100")
-}
instance Flat Int where
    size = sInt

    encode = eInt

    decode = dInt

{- |
Integers are encoded just as the fixed size Ints.

>>> test (0::Integer)
(True,8,"00000000")

>>> test (-1::Integer)
(True,8,"00000001")

>>> test (1::Integer)
(True,8,"00000010")

>>> test (-(2^4)::Integer)
(True,8,"00011111")

>>> test (2^4::Integer)
(True,8,"00100000")

>>> test (-(2^120)::Integer)
(True,144,"11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 00000011")

>>> test (2^120::Integer)
(True,144,"10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 10000000 00000100")
-}
instance Flat Integer where
    size = sInteger

    encode = eInteger

    decode = dInteger

{- |
>>> test (0::Int8)
(True,8,"00000000")

>>> test (127::Int8)
(True,8,"11111110")

>>> test (-128::Int8)
(True,8,"11111111")
-}
instance Flat Int8 where
    encode = eInt8

    decode = dInt8

    size = sInt8

{- |
>>> test (0::Int16)
(True,8,"00000000")

>>> test (1::Int16)
(True,8,"00000010")

>>> test (-1::Int16)
(True,8,"00000001")

>>> test (minBound::Int16)
(True,24,"11111111 11111111 00000011")

equivalent to 0b1111111111111111

>>> test (maxBound::Int16)
(True,24,"11111110 11111111 00000011")

equivalent to 0b1111111111111110
-}
instance Flat Int16 where
    size = sInt16

    encode = eInt16

    decode = dInt16

{- |
>>> test (0::Int32)
(True,8,"00000000")

>>> test (minBound::Int32)
(True,40,"11111111 11111111 11111111 11111111 00001111")

>>> test (maxBound::Int32)
(True,40,"11111110 11111111 11111111 11111111 00001111")
-}
instance Flat Int32 where
    size = sInt32

    encode = eInt32

    decode = dInt32

{- |
>>> test (0::Int64)
(True,8,"00000000")

>>> test (minBound::Int64)
(True,80,"11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 00000001")

>>> test (maxBound::Int64)
(True,80,"11111110 11111111 11111111 11111111 11111111 11111111 11111111 11111111 11111111 00000001")
-}
instance Flat Int64 where
    size = sInt64

    encode = eInt64

    decode = dInt64

{- |
Floats are encoded as standard IEEE binary32 values:

@
IEEE_754_binary32 ≡ IEEE_754_binary32 {sign :: Sign,
                                        exponent :: MostSignificantFirst Bits8,
                                        fraction :: MostSignificantFirst Bits23}
@

>>> test (0::Float)
(True,32,"00000000 00000000 00000000 00000000")

>>> test (1.4012984643E-45::Float)
(True,32,"00000000 00000000 00000000 00000001")

>>> test (1.1754942107E-38::Float)
(True,32,"00000000 01111111 11111111 11111111")
-}
instance Flat Float where
    size = sFloat

    encode = eFloat

    decode = dFloat

{- |
Doubles are encoded as standard IEEE binary64 values:

@
IEEE_754_binary64 ≡ IEEE_754_binary64 {sign :: Sign,
                                        exponent :: MostSignificantFirst Bits11,
                                        fraction :: MostSignificantFirst Bits52}
@
-}
instance Flat Double where
    size = sDouble

    encode = eDouble

    decode = dDouble

{- |
>>> test (4 :+ 2 :: Complex Word8)
(True,16,"00000100 00000010")
-}
instance Flat a => Flat (Complex a)

{- |
Ratios are encoded as tuples of (numerator,denominator)

>>> test (3%4::Ratio Word8)
(True,16,"00000011 00000100")
-}
instance (Integral a, Flat a) => Flat (Ratio a) where
    size a = size (numerator a, denominator a)

    encode a = encode (numerator a, denominator a)

    -- decode = uncurry (%) <$> decode
    decode = liftM2 (%) decode decode

{- |
>>> test ([]::[Bool])
(True,1,"0")

>>> test [False,False]
(True,5,"10100")

This instance and other similar ones are declared as @OVERLAPPABLE@, because for better encoding/decoding
performance it can be useful to declare instances of concrete types, such as @[Char]@ (not provided out of the box).
-}
instance {-# OVERLAPPABLE #-} Flat a => Flat [a]

{-
>>> import Weigh
>>> flat [1..10::Int]
-}


-- Generic list instance (stack overflows with ETA, see https://github.com/typelead/eta/issues/901)
-- where
--size [] n = n+1
--size (h:t) n = trampoline size t (trampoline size h (n+1))
-- size = sizeListWith size -- foldl' (\n e -> ) n
-- encode = error "BAD"
-- encode = trampoline . encodeListWith encode
-- decode = decodeListWith decode
-- sizeListWith siz l n = foldl' (\n e -> 1 + n + siz e 0) n l
-- #ifdef ETA_VERSION
-- import Data.Function(trampoline)
-- import GHC.IO(trampolineIO)
-- #else
-- trampoline = id
-- trampolineIO = id
-- #endif

-- #if MIN_VERSION_base(4,9,0)

{- |
>>> test (B.fromList [True])
(True,2,"10")

>>> test (B.fromList [False,False])
(True,4,"0100")
-}
instance {-# OVERLAPPABLE #-} Flat a => Flat (B.NonEmpty a)

-- #endif

{- |
Tuples are supported up to 7 elements.

>>> test (False,())
(True,1,"0")

>>> test ((),())
(True,0,"")

"7 elements tuples ought to be enough for anybody" (Bill Gates - apocryphal)

>>> test (False,True,True,True,False,True,True)
(True,7,"0111011")

tst (1::Int,"2","3","4","5","6","7","8")
...error
-}

-- Not sure if these should be OVERLAPPABLE
instance {-# OVERLAPPABLE #-} (Flat a, Flat b) => Flat (a, b)

instance {-# OVERLAPPABLE #-} (Flat a, Flat b, Flat c) => Flat (a, b, c)

instance
    {-# OVERLAPPABLE #-}
    (Flat a, Flat b, Flat c, Flat d) =>
    Flat (a, b, c, d)

instance
    {-# OVERLAPPABLE #-}
    (Flat a, Flat b, Flat c, Flat d, Flat e) =>
    Flat (a, b, c, d, e)

instance
    {-# OVERLAPPABLE #-}
    (Flat a, Flat b, Flat c, Flat d, Flat e, Flat f) =>
    Flat (a, b, c, d, e, f)

instance
    {-# OVERLAPPABLE #-}
    ( Flat a
    , Flat b
    , Flat c
    , Flat d
    , Flat e
    , Flat f
    , Flat g
    ) =>
    Flat (a, b, c, d, e, f, g)
