-- Types used for C FFI.
module Foreign.C.Types(
 CChar(..),  CSChar(..),  CUChar(..),
 CShort(..), CUShort(..),
 CInt(..),   CUInt(..),
 CLong(..),  CULong(..),
 CPtrdiff(..),
 CSize(..),  CSSize(..),
 CLLong(..), CULLong(..),
 CIntPtr(..), CUIntPtr(..),
 CFloat(..), CDouble(..),
 CTime(..),
 intToCSize, cSizeToInt,
 ) where
import qualified Prelude()
import Primitives
import Data.Bool
import Data.Coerce
import Data.Enum
import Data.Eq
import Data.Int
import Data.Integral
import Data.Num
import Data.Ord
import Data.Real
import Data.Word
import Data.FloatW

-- The MicroHs Word type is the "natural" architecture word size;
-- it is the same as the pointer difference type.
-- And Int is the natural signed word size.
newtype CChar    = CChar    Char
  deriving (Eq, Ord, Enum)
newtype CSChar   = CSChar   Int
  deriving (Eq, Ord, Enum)
newtype CUChar   = CUChar   Word
  deriving (Eq, Ord, Enum)
newtype CShort   = CShort   Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CUShort  = CUShort  Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CInt     = CInt     Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CUInt    = CUInt    Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CLong    = CLong    Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CULong   = CULong   Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CPtrdiff = CPtrdiff Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CSize    = CSize    Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CSSize   = CSSize   Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CLLong   = CLLong   Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CULLong  = CULLong  Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CIntPtr  = CIntPtr  Int
  deriving (Eq, Ord, Enum, Num, Integral, Real)
newtype CUIntPtr = CUIntPtr Word
  deriving (Eq, Ord, Enum, Num, Integral, Real)

-- XXX This is really platform specific
newtype CTime = CTime Int
  deriving (Eq, Ord)

-- XXX only one of these is actually correct
newtype CFloat   = CFloat   FloatW
  deriving (Eq, Ord, Num)
newtype CDouble  = CDouble  FloatW
  deriving (Eq, Ord, Num)

-- Temporary conversion functions.
intToCSize :: Int -> CSize
intToCSize i = CSize (primIntToWord i)

cSizeToInt :: CSize -> Int
cSizeToInt (CSize i) = primWordToInt i
