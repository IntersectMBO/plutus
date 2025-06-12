module Data.Double(Double) where
import qualified Prelude()
import Data.Enum
import Data.Eq
import Data.FloatW
import Data.Floating
import Data.Fractional
import Data.Num
import Data.Ord
import Data.Real
import Data.RealFloat
import Data.RealFrac
import Mhs.Builtin
import Text.Show

newtype Double = D FloatW
  deriving(Eq, Ord, Num, Fractional, Real, RealFrac, Floating, RealFloat, Enum)

instance Show Double where
  showsPrec p (D x) = showsPrec p x
