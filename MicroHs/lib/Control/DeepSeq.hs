module Control.DeepSeq (
  NFData(..), NFData1(..), NFData2(..),
  deepseq,
  force,
  ($!!),
  (<$!!>),
  rwhnf,
  rnf1,
  rnf2,
) where
import Control.Applicative
import Control.DeepSeq.Class
import Control.Monad
import Data.Bool
import Data.Char
import Data.Complex
import Data.Double
import Data.Either
import Data.Fixed
import Data.Float
import Data.Function
import Data.Int
import Data.Integer
import Data.List
import Data.List.NonEmpty
import Data.Maybe
import Data.Ord
import Data.Proxy
import Data.Ratio
import Data.Real
import Data.Tuple
import Data.Word
import Prelude qualified ()

infixl 4 <$!!>

(<$!!>) :: (Monad m, NFData b) => (a -> b) -> m a -> m b
f <$!!> m = m >>= \x -> pure $!! f x

rwhnf :: a -> ()
rwhnf a = a `seq` ()

instance NFData Float
instance NFData Int8
instance NFData Int16
instance NFData Int32
instance NFData Int64
instance NFData Word8
instance NFData Word16
instance NFData Word32
instance NFData Word64

instance NFData (Proxy a) where rnf Proxy = ()
instance NFData1 Proxy where liftRnf _ Proxy = ()

instance NFData1 Maybe where
  liftRnf _ Nothing     = ()
  liftRnf rnfa (Just a) = rnfa a

instance NFData1 [] where
  liftRnf rnfa = foldr (\ x r -> rnfa x `seq` r) ()

instance NFData2 Either where
  liftRnf2 rnfa _ (Left  a) = rnfa a
  liftRnf2 _ rnfb (Right b) = rnfb b

instance (NFData a) => NFData (Complex a) where
  rnf = rnf1
instance NFData1 Complex where
  liftRnf rnfa (x :+ y) = rnfa x `seq` rnfa y

instance NFData a => NFData (NonEmpty a) where
  rnf = rnf1
instance NFData1 NonEmpty where
  liftRnf rnfa = liftRnf rnfa . toList

-- Fixed is a newtype over Integer
instance NFData (Fixed a)
--  rnf = rnf

{-
-- | @since 1.4.3.0
instance NFData (a :~~: b)

-- | @since 1.4.3.0
instance NFData1 ((:~~:) a) where liftRnf _ = rwhnf

-- | @since 1.4.3.0
instance NFData2 (:~~:) where liftRnf2 _ _ = rwhnf

-- | @since 1.4.0.0
instance NFData a => NFData (Identity a) where
  rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Identity where
  liftRnf r = r . runIdentity

-- | Defined as @'rnf' = 'absurd'@.
--
-- @since 1.4.0.0
instance NFData Void where
  rnf = absurd

-- | @since 1.4.0.0
instance NFData Natural

-- | @since 1.3.0.0
instance NFData (Fixed a)

-- | @since 1.4.3.0
instance NFData1 Fixed where liftRnf _ = rwhnf

-- | This instance is for convenience and consistency with 'seq'.
--  This assumes that WHNF is equivalent to NF for functions.
--
--  @since 1.3.0.0
instance NFData (a -> b)

-- Rational and complex numbers.

-- | Available on @base >=4.9@
--
-- @since 1.4.3.0
instance NFData1 Ratio where
  liftRnf r x = r (numerator x) `seq` r (denominator x)

-- | @since 1.4.3.0
instance (NFData1 f, NFData1 g) => NFData1 (Compose f g) where
  liftRnf r = liftRnf (liftRnf r) . getCompose

-- | Note: in @deepseq-1.5.0.0@ this instance's superclasses were changed.
--
-- @since 1.4.3.0
instance (NFData (f (g a))) => NFData (Compose f g a) where
  rnf (Compose fga) = rnf fga

-- | @since 1.4.3.0
instance (NFData1 f, NFData1 g) => NFData1 (Functor.Sum f g) where
  liftRnf rnf0 (Functor.InL l) = liftRnf rnf0 l
  liftRnf rnf0 (Functor.InR r) = liftRnf rnf0 r

-- | Note: in @deepseq-1.5.0.0@ this instance's superclasses were changed.
--
-- @since 1.4.3.0
instance (NFData (f a), NFData (g a)) => NFData (Functor.Sum f g a) where
  rnf (Functor.InL fa) = rnf fa
  rnf (Functor.InR ga) = rnf ga

-- | @since 1.4.3.0
instance (NFData1 f, NFData1 g) => NFData1 (Functor.Product f g) where
  liftRnf rnf0 (Functor.Pair f g) = liftRnf rnf0 f `seq` liftRnf rnf0 g

-- | Note: in @deepseq-1.5.0.0@ this instance's superclasses were changed.
--
-- @since 1.4.3.0
instance (NFData (f a), NFData (g a)) => NFData (Functor.Product f g a) where
  rnf (Functor.Pair fa ga) = rnf fa `seq` rnf ga

instance NFData a => NFData (Ratio a) where
  rnf x = rnf (numerator x, denominator x)

instance (NFData a) => NFData (Complex a) where
  rnf (x :+ y) = rnf x `seq` rnf y `seq` ()

instance NFData a => NFData (Maybe a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Maybe where
  liftRnf _r Nothing = ()
  liftRnf r (Just x) = r x

instance (NFData a, NFData b) => NFData (Either a b) where rnf = rnf1

-- | @since 1.4.3.0
instance (NFData a) => NFData1 (Either a) where liftRnf = liftRnf2 rnf

-- | @since 1.4.3.0
instance NFData2 Either where
  liftRnf2 l _r (Left x) = l x
  liftRnf2 _l r (Right y) = r y

-- | @since 1.3.0.0
instance NFData Data.Version.Version where
  rnf (Data.Version.Version branch tags) = rnf branch `seq` rnf tags

instance NFData a => NFData [a] where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 [] where
  liftRnf f = foldr (\x r -> f x `seq` r) ()
  {-# INLINABLE liftRnf #-}

-- | @since 1.4.0.0
instance NFData a => NFData (ZipList a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 ZipList where
  liftRnf r = liftRnf r . getZipList

-- | @since 1.4.0.0
instance NFData a => NFData (Const a b) where
  rnf = rnf . getConst

-- | @since 1.4.3.0
instance NFData a => NFData1 (Const a) where
  liftRnf _ = rnf . getConst

-- | @since 1.4.3.0
instance NFData2 Const where
  liftRnf2 r _ = r . getConst

-- We should use MIN_VERSION array(0,5,1,1) but that's not possible.
-- There isn't an underscore to not break C preprocessor
instance (NFData a, NFData b) => NFData (Array a b) where
  rnf x = rnf (bounds x, Data.Array.elems x)

-- | @since 1.4.3.0
instance (NFData a) => NFData1 (Array a) where
  liftRnf r x = rnf (bounds x) `seq` liftRnf r (Data.Array.elems x)

-- | @since 1.4.3.0
instance NFData2 Array where
  liftRnf2 r r' x = liftRnf2 r r (bounds x) `seq` liftRnf r' (Data.Array.elems x)

-- | @since 1.4.0.0
instance NFData a => NFData (Down a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Down where
  liftRnf r (Down x) = r x

-- | @since 1.4.0.0
instance NFData a => NFData (Dual a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Dual where
  liftRnf r (Dual x) = r x

-- | @since 1.4.0.0
instance NFData a => NFData (Mon.First a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Mon.First where
  liftRnf r (Mon.First x) = liftRnf r x

-- | @since 1.4.0.0
instance NFData a => NFData (Mon.Last a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Mon.Last where
  liftRnf r (Mon.Last x) = liftRnf r x

-- | @since 1.4.0.0
instance NFData Any where rnf = rnf . getAny

-- | @since 1.4.0.0
instance NFData All where rnf = rnf . getAll

-- | @since 1.4.0.0
instance NFData a => NFData (Sum a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Sum where
  liftRnf r (Sum x) = r x

-- | @since 1.4.0.0
instance NFData a => NFData (Product a) where rnf = rnf1

-- | @since 1.4.3.0
instance NFData1 Product where
  liftRnf r (Product x) = r x

-- | @since 1.4.0.0
instance NFData (StableName a) where
  rnf = rwhnf -- assumes `data StableName a = StableName (StableName# a)`

-- | @since 1.4.3.0
instance NFData1 StableName where
  liftRnf _ = rwhnf

-- | @since 1.4.0.0
instance NFData ThreadId where
  rnf = rwhnf -- assumes `data ThreadId = ThreadId ThreadId#`

-- | @since 1.4.0.0
instance NFData Unique where
  rnf = rwhnf -- assumes `newtype Unique = Unique Integer`

-- | __NOTE__: Prior to @deepseq-1.4.4.0@ this instance was only defined for @base-4.8.0.0@ and later.
--
-- @since 1.4.0.0
instance NFData TypeRep where
  rnf tyrep = rnfTypeRep tyrep

-- | __NOTE__: Prior to @deepseq-1.4.4.0@ this instance was only defined for @base-4.8.0.0@ and later.
--
-- @since 1.4.0.0
instance NFData TyCon where
  rnf tycon = rnfTyCon tycon

-- | @since 1.4.8.0
instance NFData (Reflection.TypeRep a) where
  rnf tr = Reflection.rnfTypeRep tr

-- | @since 1.4.8.0
instance NFData Reflection.Module where
  rnf modul = Reflection.rnfModule modul

-- | __NOTE__: Only strict in the reference and not the referenced value.
--
-- @since 1.4.2.0
instance NFData (IORef a) where
  rnf = rwhnf

-- | @since 1.4.3.0
instance NFData1 IORef where
  liftRnf _ = rwhnf

-- | __NOTE__: Only strict in the reference and not the referenced value.
--
-- @since 1.4.2.0
instance NFData (STRef s a) where
  rnf = rwhnf

-- | @since 1.4.3.0
instance NFData1 (STRef s) where
  liftRnf _ = rwhnf

-- | @since 1.4.3.0
instance NFData2 STRef where
  liftRnf2 _ _ = rwhnf

-- | __NOTE__: Only strict in the reference and not the referenced value.
--
-- @since 1.4.2.0
instance NFData (MVar a) where
  rnf = rwhnf

-- | @since 1.4.3.0
instance NFData1 MVar where
  liftRnf _ = rwhnf

----------------------------------------------------------------------------
-- GHC Specifics

-- | @since 1.4.0.0
instance NFData Fingerprint where
  rnf (Fingerprint _ _) = ()

----------------------------------------------------------------------------
-- Foreign.Ptr

-- | @since 1.4.2.0
instance NFData (Ptr a) where
  rnf = rwhnf

-- | @since 1.4.3.0
instance NFData1 Ptr where
  liftRnf _ = rwhnf

-- | @since 1.4.2.0
instance NFData (FunPtr a) where
  rnf = rwhnf

-- | @since 1.4.3.0
instance NFData1 FunPtr where
  liftRnf _ = rwhnf

----------------------------------------------------------------------------
-- Foreign.C.Types

-- | @since 1.4.0.0
instance NFData CChar

-- | @since 1.4.0.0
instance NFData CSChar

-- | @since 1.4.0.0
instance NFData CUChar

-- | @since 1.4.0.0
instance NFData CShort

-- | @since 1.4.0.0
instance NFData CUShort

-- | @since 1.4.0.0
instance NFData CInt

-- | @since 1.4.0.0
instance NFData CUInt

-- | @since 1.4.0.0
instance NFData CLong

-- | @since 1.4.0.0
instance NFData CULong

-- | @since 1.4.0.0
instance NFData CPtrdiff

-- | @since 1.4.0.0
instance NFData CSize

-- | @since 1.4.0.0
instance NFData CWchar

-- | @since 1.4.0.0
instance NFData CSigAtomic

-- | @since 1.4.0.0
instance NFData CLLong

-- | @since 1.4.0.0
instance NFData CULLong

-- | @since 1.4.0.0
instance NFData CIntPtr

-- | @since 1.4.0.0
instance NFData CUIntPtr

-- | @since 1.4.0.0
instance NFData CIntMax

-- | @since 1.4.0.0
instance NFData CUIntMax

-- | @since 1.4.0.0
instance NFData CClock

-- | @since 1.4.0.0
instance NFData CTime

-- | @since 1.4.0.0
instance NFData CUSeconds

-- | @since 1.4.0.0
instance NFData CSUSeconds

-- | @since 1.4.0.0
instance NFData CFloat

-- | @since 1.4.0.0
instance NFData CDouble

-- NOTE: The types `CFile`, `CFPos`, and `CJmpBuf` below are not
-- newtype wrappers rather defined as field-less single-constructor
-- types.

-- | @since 1.4.0.0
instance NFData CFile

-- | @since 1.4.0.0
instance NFData CFpos

-- | @since 1.4.0.0
instance NFData CJmpBuf

-- | @since 1.4.3.0
instance NFData CBool

----------------------------------------------------------------------------
-- System.Exit

-- | @since 1.4.2.0
instance NFData ExitCode where
  rnf (ExitFailure n) = rnf n
  rnf ExitSuccess = ()

-}

----------------------------------------------------------------------------
-- Tuples

instance NFData a => NFData (Solo a) where
  rnf (MkSolo a) = rnf a

instance (NFData a1, NFData a2, NFData a3) =>
         NFData (a1, a2, a3) where
  rnf (a1, a2, a3) = rnf a1 `seq` rnf a2 `seq` rnf a3

instance (NFData a1, NFData a2, NFData a3, NFData a4) =>
         NFData (a1, a2, a3, a4) where
  rnf (a1, a2, a3, a4) = rnf a1 `seq` rnf a2 `seq` rnf a3 `seq` rnf a4

instance (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5) =>
         NFData (a1, a2, a3, a4, a5) where
  rnf (a1, a2, a3, a4, a5) = rnf a1 `seq` rnf a2 `seq` rnf a3 `seq` rnf a4 `seq` rnf a5

----------------------------------------------------------------------------
-- NFData1 and NFData 2 are not totally compatible with GHC, but they sometimes work.
-- To be compatible, we need QuantifiedConstraints.

class NFData1 f where
  liftRnf :: (a -> ()) -> f a -> ()

class NFData2 p where
  liftRnf2 :: (a -> ()) -> (b -> ()) -> p a b -> ()

rnf1 :: (NFData1 f, NFData a) => f a -> ()
rnf1 = liftRnf rnf

rnf2 :: (NFData2 p, NFData a, NFData b) => p a b -> ()
rnf2 = liftRnf2 rnf rnf
