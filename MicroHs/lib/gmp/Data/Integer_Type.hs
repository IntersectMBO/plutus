module Data.Integer_Type(
  Integer(..),
  MPZ, newMPZ,
  _intToInteger, _wordToInteger, _integerToInt, _integerToWord,
  _integerToFloatW,
  ) where
import qualified Prelude()
import Primitives
--import Foreign.ForeignPtr
--import Mhs.Builtin
--import System.IO.Unsafe

-- We cannot import Foreign.ForeignPtr; it is circular.
withForeignPtr :: ForeignPtr a -> (Ptr a -> IO b) -> IO b
withForeignPtr fp io =
  io (primForeignPtrToPtr fp) `primBind` \ b ->
  primSeq fp (primReturn b)

-----

data MPZ

newtype Integer = I (ForeignPtr MPZ)

foreign import capi "new_mpz"         new_mpz         :: IO (Ptr MPZ)  -- it really returns a ForeignPtr
foreign import capi "mpz_init_set_si" mpz_init_set_si :: Ptr MPZ -> Int -> IO ()
foreign import capi "mpz_init_set_ui" mpz_init_set_ui :: Ptr MPZ -> Word -> IO ()
foreign import capi "mpz_get_si"      mpz_get_si      :: Ptr MPZ -> IO Int
foreign import capi "mpz_get_ui"      mpz_get_ui      :: Ptr MPZ -> IO Word
foreign import capi "mpz_get_d"       mpz_get_d       :: Ptr MPZ -> IO FloatW

newMPZ :: IO (ForeignPtr MPZ)
newMPZ =
  new_mpz `primBind` \ x ->
  primReturn (primUnsafeCoerce x)

_intToInteger :: Int -> Integer
_intToInteger i = primPerformIO (
  newMPZ `primBind` \ x ->
  withForeignPtr x ( \ p -> mpz_init_set_si p i) `primThen`
  primReturn (I x)
  )

_wordToInteger :: Word -> Integer
_wordToInteger i = primPerformIO (do
  newMPZ `primBind` \ x ->
  withForeignPtr x ( \ p -> mpz_init_set_ui p i) `primThen`
  primReturn (I x)
  )

_integerToInt :: Integer -> Int
_integerToInt (I x) = primPerformIO (withForeignPtr x mpz_get_si)

_integerToWord :: Integer -> Word
_integerToWord (I x) = primPerformIO (withForeignPtr x mpz_get_ui)

_integerToFloatW :: Integer -> FloatW
_integerToFloatW (I x) = primPerformIO (withForeignPtr x mpz_get_d)
