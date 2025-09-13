{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE Trustworthy               #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

-- |Generics-based generation of Flat instances
module PlutusCore.Flat.Class
  (
  -- * The Flat class
    Flat(..)
  , getSize
  , module GHC.Generics
  , GFlatEncode,GFlatDecode,GFlatSize
  )
where

import Data.Bits (Bits (unsafeShiftL, (.|.)))
import Data.Word (Word16)
import GHC.Generics
import GHC.TypeLits (Nat, type (+), type (<=))
import PlutusCore.Flat.Decoder.Prim (ConsState (..), consBits, consBool, consClose, consOpen, dBool)
import PlutusCore.Flat.Decoder.Types (Get)
import PlutusCore.Flat.Encoder (Encoding, NumBits, eBits16, mempty)
import Prelude hiding (mempty)

#if MIN_VERSION_base(4,9,0)
import Data.Kind
#endif

#if ! MIN_VERSION_base(4,11,0)
import Data.Semigroup ((<>))
#endif


-- External and Internal inlining
#define INL 2
-- Internal inlining
-- #define INL 1
-- No inlining
-- #define INL 0

#if INL == 1
import GHC.Exts (inline)
#endif

-- import           Data.Proxy

-- |Calculate the maximum size in bits of the serialisation of the value
getSize :: Flat a => a -> NumBits
getSize a = size a 0

{-| Class of types that can be encoded/decoded

Encoding a value involves three steps:

* calculate the maximum size of the serialised value, using `size`

* preallocate a buffer of the required size

* encode the value in the buffer, using `encode`
-}
class Flat a where
    -- |Return the encoding corrresponding to the value
    encode :: a -> Encoding
    default encode :: (Generic a, GFlatEncode (Rep a)) => a -> Encoding
    encode = gencode . from

    -- |Decode a value
    decode :: Get a
    default decode :: (Generic a, GFlatDecode (Rep a)) => Get a
    decode = to `fmap` gget

    -- |Add maximum size in bits of the value to the total count
    --
    --  Used to calculated maximum buffer size before encoding
    size :: a -> NumBits -> NumBits
    default size :: (Generic a, GFlatSize (Rep a)) => a -> NumBits -> NumBits
    size !x !n = gsize n $ from x

#if INL>=2
    -- With these, generated code is optimised for specific data types (e.g.: Tree Bool will fuse the code of Tree and Bool)
    -- This can improve performance very significantly (up to 10X) but also increases compilation times.
    {-# INLINE size #-}
    {-# INLINE decode #-}
    {-# INLINE encode #-}
#elif INL == 1
#elif INL == 0
    {-# NOINLINE size #-}
    {-# NOINLINE decode #-}
    {-# NOINLINE encode #-}
#endif

-- |Generic Encoder
class GFlatEncode f where gencode :: f a -> Encoding

instance {-# OVERLAPPABLE #-} GFlatEncode f => GFlatEncode (M1 i c f) where
      gencode = gencode . unM1
      {-# INLINE gencode #-}

  -- Special case, single constructor datatype
instance {-# OVERLAPPING #-} GFlatEncode a => GFlatEncode (D1 i (C1 c a)) where
      gencode = gencode . unM1 . unM1
      {-# INLINE gencode #-}

  -- Type without constructors
instance GFlatEncode V1 where
      gencode = unused
      {-# INLINE gencode #-}

  -- Constructor without arguments
instance GFlatEncode U1 where
      gencode U1 = mempty
      {-# INLINE gencode #-}

instance Flat a => GFlatEncode (K1 i a) where
      {-# INLINE gencode #-}
#if INL == 1
      gencode x = inline encode (unK1 x)
#else
      gencode = encode . unK1
#endif

instance (GFlatEncode a, GFlatEncode b) => GFlatEncode (a :*: b) where
      --gencode (!x :*: (!y)) = gencode x <++> gencode y
      gencode (x :*: y) = gencode x <> gencode y
      {-# INLINE gencode #-}

instance (NumConstructors (a :+: b) <= 512,GFlatEncodeSum (a :+: b)) => GFlatEncode (a :+: b) where
-- instance (GFlatEncodeSum (a :+: b)) => GFlatEncode (a :+: b) where
      gencode = gencodeSum 0 0
      {-# INLINE gencode #-}

-- Constructor Encoding
class GFlatEncodeSum f where
  gencodeSum :: Word16 -> NumBits -> f a -> Encoding

instance (GFlatEncodeSum a, GFlatEncodeSum b) => GFlatEncodeSum (a :+: b) where
  gencodeSum !code !numBits s = case s of
                           L1 !x -> gencodeSum (code `unsafeShiftL` 1) (numBits+1) x
                           R1 !x -> gencodeSum ((code `unsafeShiftL` 1) .|. 1) (numBits+1) x
  {-# INLINE  gencodeSum #-}

instance GFlatEncode a => GFlatEncodeSum (C1 c a) where
  gencodeSum !code !numBits x = eBits16 numBits code <> gencode x
  {-# INLINE  gencodeSum #-}

-- |Generic Decoding
class GFlatDecode f where
  gget :: Get (f t)

-- |Metadata (constructor name, etc)
instance GFlatDecode a => GFlatDecode (M1 i c a) where
    gget = M1 <$> gget
    {-# INLINE  gget #-}

-- |Type without constructors
instance GFlatDecode V1 where
    gget = unused
    {-# INLINE  gget #-}

-- |Constructor without arguments
instance GFlatDecode U1 where
    gget = pure U1
    {-# INLINE  gget #-}

-- |Product: constructor with parameters
instance (GFlatDecode a, GFlatDecode b) => GFlatDecode (a :*: b) where
  gget = (:*:) <$> gget <*> gget
  {-# INLINE gget #-}

-- |Constants, additional parameters, and rank-1 recursion
instance Flat a => GFlatDecode (K1 i a) where
#if INL == 1
  gget = K1 <$> inline decode
#else
  gget = K1 <$> decode
#endif
  {-# INLINE gget #-}


-- Different valid decoding setups
-- #define DEC_BOOLG
-- #define DEC_BOOL

-- #define DEC_BOOLG
-- #define DEC_BOOL
-- #define DEC_BOOL48

-- #define DEC_CONS
-- #define DEC_BOOLC
-- #define DEC_BOOL

-- #define DEC_CONS
-- #define DEC_BOOLC
-- #define DEC_BOOL
-- #define DEC_BOOL48

-- #define DEC_CONS

-- #define DEC_CONS
-- #define DEC_CONS48

#define DEC_CONS
#define DEC_CONS48
#define DEC_BOOLC
#define DEC_BOOL

#ifdef DEC_BOOLG
instance (GFlatDecode a, GFlatDecode b) => GFlatDecode (a :+: b)
#endif

#ifdef DEC_BOOLC
-- Special case for data types with two constructors
instance {-# OVERLAPPING #-} (GFlatDecode a,GFlatDecode b) => GFlatDecode (C1 m1 a :+: C1 m2 b)
#endif

#ifdef DEC_BOOL
  where
      gget = do
        -- error "DECODE2_C2"
        !tag <- dBool
        !r <- if tag then R1 <$> gget else L1 <$> gget
        return r
      {-# INLINE gget #-}
#endif

#ifdef DEC_CONS
-- | Data types with up to 512 constructors
-- Uses a custom constructor decoding state
-- instance {-# OVERLAPPABLE #-} (GFlatDecodeSum (a :+: b),GFlatDecode a, GFlatDecode b) => GFlatDecode (a :+: b) where
instance {-# OVERLAPPABLE #-} (NumConstructors (a :+: b) <= 512, GFlatDecodeSum (a :+: b)) => GFlatDecode (a :+: b) where
  gget = do
    cs <- consOpen
    getSum cs
  {-# INLINE gget #-}

-- |Constructor Decoder
class GFlatDecodeSum f where
    getSum :: ConsState -> Get (f a)

#ifdef DEC_CONS48

-- Decode constructors in groups of 2 or 3 bits
-- Significantly reduce instance compilation time and slightly improve execution times
instance {-# OVERLAPPING #-} (GFlatDecodeSum n1,GFlatDecodeSum n2,GFlatDecodeSum n3,GFlatDecodeSum n4) => GFlatDecodeSum ((n1 :+: n2) :+: (n3 :+: n4)) -- where -- getSum = undefined
      where
          getSum cs = do
            -- error "DECODE4"
            let (cs',tag) = consBits cs 2
            case tag of
              0 -> L1 . L1 <$> getSum cs'
              1 -> L1 . R1 <$> getSum cs'
              2 -> R1 . L1 <$> getSum cs'
              _ -> R1 . R1 <$> getSum cs'
          {-# INLINE getSum #-}

instance {-# OVERLAPPING #-} (GFlatDecodeSum n1,GFlatDecodeSum n2,GFlatDecodeSum n3,GFlatDecodeSum n4,GFlatDecodeSum n5,GFlatDecodeSum n6,GFlatDecodeSum n7,GFlatDecodeSum n8) => GFlatDecodeSum (((n1 :+: n2) :+: (n3 :+: n4)) :+: ((n5 :+: n6) :+: (n7 :+: n8))) -- where -- getSum cs = undefined
     where
      getSum cs = do
        --error "DECODE8"
        let (cs',tag) = consBits cs 3
        case tag of
          0 -> L1 . L1 . L1 <$> getSum cs'
          1 -> L1 . L1 . R1 <$> getSum cs'
          2 -> L1 . R1 . L1 <$> getSum cs'
          3 -> L1 . R1 . R1 <$> getSum cs'
          4 -> R1 . L1 . L1 <$> getSum cs'
          5 -> R1 . L1 . R1 <$> getSum cs'
          6 -> R1 . R1 . L1 <$> getSum cs'
          _ -> R1 . R1 . R1 <$> getSum cs'
      {-# INLINE getSum #-}

instance {-# OVERLAPPABLE #-} (GFlatDecodeSum a, GFlatDecodeSum b) => GFlatDecodeSum (a :+: b) where
#else
instance (GFlatDecodeSum a, GFlatDecodeSum b) => GFlatDecodeSum (a :+: b) where
#endif

  getSum cs = do
    let (cs',tag) = consBool cs
    if tag then R1 <$> getSum cs' else L1 <$> getSum cs'
  {-# INLINE getSum #-}


instance GFlatDecode a => GFlatDecodeSum (C1 c a) where
    getSum (ConsState _ usedBits) = consClose usedBits >> gget
    {-# INLINE getSum #-}
#endif

#ifdef DEC_BOOL48
instance {-# OVERLAPPING #-} (GFlatDecode n1,GFlatDecode n2,GFlatDecode n3,GFlatDecode n4) => GFlatDecode ((n1 :+: n2) :+: (n3 :+: n4)) -- where -- gget = undefined
  where
      gget = do
        -- error "DECODE4"
        !tag <- dBEBits8 2
        case tag of
          0 -> L1 <$> L1 <$> gget
          1 -> L1 <$> R1 <$> gget
          2 -> R1 <$> L1 <$> gget
          _ -> R1 <$> R1 <$> gget
      {-# INLINE gget #-}

instance {-# OVERLAPPING #-} (GFlatDecode n1,GFlatDecode n2,GFlatDecode n3,GFlatDecode n4,GFlatDecode n5,GFlatDecode n6,GFlatDecode n7,GFlatDecode n8) => GFlatDecode (((n1 :+: n2) :+: (n3 :+: n4)) :+: ((n5 :+: n6) :+: (n7 :+: n8))) -- where -- gget = undefined
 where
  gget = do
    --error "DECODE8"
    !tag <- dBEBits8 3
    case tag of
      0 -> L1 <$> L1 <$> L1 <$> gget
      1 -> L1 <$> L1 <$> R1 <$> gget
      2 -> L1 <$> R1 <$> L1 <$> gget
      3 -> L1 <$> R1 <$> R1 <$> gget
      4 -> R1 <$> L1 <$> L1 <$> gget
      5 -> R1 <$> L1 <$> R1 <$> gget
      6 -> R1 <$> R1 <$> L1 <$> gget
      _ -> R1 <$> R1 <$> R1 <$> gget
  {-# INLINE gget #-}
#endif

-- |Calculate the number of bits required for the serialisation of a value
-- Implemented as a function that adds the maximum size to a running total
class GFlatSize f where gsize :: NumBits -> f a -> NumBits

-- |Skip metadata
instance GFlatSize f => GFlatSize (M1 i c f) where
    gsize !n = gsize n . unM1
    {-# INLINE gsize #-}

-- |Type without constructors
instance GFlatSize V1 where
    gsize !n _ = n
    {-# INLINE gsize #-}

-- |Constructor without arguments
instance GFlatSize U1 where
    gsize !n _ = n
    {-# INLINE gsize #-}

-- |Skip metadata
instance Flat a => GFlatSize (K1 i a) where
#if INL == 1
  gsize !n x = inline size (unK1 x) n
#else
  gsize !n x = size (unK1 x) n
#endif
  {-# INLINE gsize #-}

instance (GFlatSize a, GFlatSize b) => GFlatSize (a :*: b) where
    gsize !n (x :*: y) =
      let !n' = gsize n x
      in gsize n' y
      -- gsize (gsize n x) y
    {-# INLINE gsize #-}

-- Alternative 'gsize' implementations
#define SIZ_ADD
-- #define SIZ_NUM

-- #define SIZ_MAX
-- #define SIZ_MAX_VAL
-- #define SIZ_MAX_PROX

#ifdef SIZ_ADD
instance (GFlatSizeSum (a :+: b)) => GFlatSize (a :+: b) where
  gsize !n = gsizeSum n
#endif

#ifdef SIZ_NUM
instance (GFlatSizeSum (a :+: b)) => GFlatSize (a :+: b) where
  gsize !n x = n + gsizeSum 0 x
#endif

#ifdef SIZ_MAX
instance (GFlatSizeNxt (a :+: b),GFlatSizeMax (a:+:b)) => GFlatSize (a :+: b) where
  gsize !n x = gsizeNxt (gsizeMax x + n) x
  {-# INLINE gsize #-}

-- |Calculate the maximum size of a class constructor (that might be one bit more than the size of some of its constructors)
#ifdef SIZ_MAX_VAL
class GFlatSizeMax (f :: * -> *) where gsizeMax :: f a ->  NumBits

instance (GFlatSizeMax f, GFlatSizeMax g) => GFlatSizeMax (f :+: g) where
    gsizeMax _ = 1 + max (gsizeMax (undefined::f a )) (gsizeMax (undefined::g a))
    {-# INLINE gsizeMax #-}

instance (GFlatSize a) => GFlatSizeMax (C1 c a) where
    {-# INLINE gsizeMax #-}
    gsizeMax _ = 0
#endif

#ifdef SIZ_MAX_PROX
-- instance (GFlatSizeNxt (a :+: b),GFlatSizeMax (a:+:b)) => GFlatSize (a :+: b) where
--   gsize !n x = gsizeNxt (gsizeMax x + n) x
--   {-# INLINE gsize #-}


-- -- |Calculate size in bits of constructor
-- class KnownNat n => GFlatSizeMax (n :: Nat) (f :: * -> *) where gsizeMax :: f a -> Proxy n -> NumBits

-- instance (GFlatSizeMax (n + 1) a, GFlatSizeMax (n + 1) b, KnownNat n) => GFlatSizeMax n (a :+: b) where
--     gsizeMax !n x _ = case x of
--                         L1 !l -> gsizeMax n l (Proxy :: Proxy (n+1))
--                         R1 !r -> gsizeMax n r (Proxy :: Proxy (n+1))
--     {-# INLINE gsizeMax #-}

-- instance (GFlatSize a, KnownNat n) => GFlatSizeMax n (C1 c a) where
--     {-# INLINE gsizeMax #-}
--     gsizeMax !n !x _ = gsize (constructorSize + n) x
--       where
--         constructorSize :: NumBits
--         constructorSize = fromInteger (natVal (Proxy :: Proxy n))

-- class KnownNat (ConsSize f) => GFlatSizeMax (f :: * -> *) where
--   gsizeMax :: f a ->  NumBits
--   gsizeMax _ = fromInteger (natVal (Proxy :: Proxy (ConsSize f)))

type family ConsSize (a :: * -> *) :: Nat where
      ConsSize (C1 c a) = 0
      ConsSize (x :+: y) = 1 + Max (ConsSize x) (ConsSize y)

type family Max (n :: Nat) (m :: Nat) :: Nat where
   Max n m  = If (n <=? m) m n

type family If c (t::Nat) (e::Nat) where
    If 'True  t e = t
    If 'False t e = e
#endif

-- |Calculate the size of a value, not taking in account its constructor
class GFlatSizeNxt (f :: * -> *) where gsizeNxt :: NumBits -> f a ->  NumBits

instance (GFlatSizeNxt a, GFlatSizeNxt b) => GFlatSizeNxt (a :+: b) where
    gsizeNxt n x = case x of
                        L1 !l-> gsizeNxt n l
                        R1 !r-> gsizeNxt n r
    {-# INLINE gsizeNxt #-}

instance (GFlatSize a) => GFlatSizeNxt (C1 c a) where
    {-# INLINE gsizeNxt #-}
    gsizeNxt !n !x = gsize n x
#endif

-- |Calculate size in bits of constructor
-- vs proxy implementation: similar compilation time but much better run times (at least for Tree N, -70%)
#if MIN_VERSION_base(4,9,0)
class GFlatSizeSum (f :: Type -> Type) where
#else
class GFlatSizeSum (f :: * -> *) where
#endif
    gsizeSum :: NumBits -> f a ->  NumBits

instance (GFlatSizeSum a, GFlatSizeSum b)
         => GFlatSizeSum (a :+: b) where
    gsizeSum !n x = case x of
                        L1 !l-> gsizeSum (n+1) l
                        R1 !r-> gsizeSum (n+1) r
    {-# INLINE gsizeSum #-}

instance (GFlatSize a) => GFlatSizeSum (C1 c a) where
    {-# INLINE gsizeSum #-}
    gsizeSum !n !x = gsize n x


-- |Calculate number of constructors
#if MIN_VERSION_base(4,9,0)
type family NumConstructors (a :: Type -> Type) :: Nat where
#else
type family NumConstructors (a :: * -> *) :: Nat where
#endif
  NumConstructors (C1 c a) = 1
  NumConstructors (x :+: y) = NumConstructors x + NumConstructors y

unused :: forall a . a
unused = error "Now, now, you could not possibly have meant this.."
