module MHSPrelude(
  module Control.Applicative,
  module Control.DeepSeq.Class,
  module Control.Error,
  module Control.Monad,
  module Control.Monad.Fail,
  module Data.Bool,
  module Data.Bounded,
  module Data.Char,
  module Data.Double,
  module Data.Either,
  module Data.Enum,
  module Data.Eq,
  module Data.Fractional,
  module Data.Function,
  module Data.Functor,
  module Data.Int,
  module Data.Integer,
  module Data.Integral,
  module Data.List,
  module Data.Maybe,
  module Data.Monoid,
  module Data.Num,
  module Data.Ord,
  module Data.Ratio,
  module Data.Real,
  module Data.Records,
  module Data.String,
  module Data.Tuple,
  module System.IO,
  module Text.Show,
  first, second,
  usingMhs, _wordSize, _isWindows,
  appendDot,
  wantGMP,
  compiledWithMhs,
  ) where
import qualified Prelude()
--import Primitives(primRnfNoErr, primRnfErr)
import Control.Applicative(Applicative(..))
import Control.DeepSeq.Class
import Control.Error(error, undefined)
import Control.Monad(Monad(..), mapM, mapM_, sequence, sequence_, (=<<))
import Control.Monad.Fail(MonadFail(..))
import Data.Bool(Bool(..), (&&), (||), not, otherwise)
import Data.Bounded(Bounded(..))
import Data.Char(Char, String)
import Data.Double(Double)
import Data.Either(Either(..), either)
import Data.Enum(Enum(..))
import Data.Eq(Eq(..))
import Data.Fractional(Fractional(..), (^^), realToFrac)
import Data.Function(id, const, (.), flip, ($), seq, ($!), until, asTypeOf)
import Data.Functor(Functor(..), (<$>))
import Data.Int(Int)
import Data.Int.Instances
import Data.Integer(Integer)
import Data.Integral(Integral(..), fromIntegral, gcd, lcm, even, odd, (^))
import Data.List([](..), map, (++), filter, head, last, tail, init, null, length, (!!),
                 reverse, foldl, foldl1, foldr, foldr1, and, or, any, all,
                 sum, product, concat, concatMap, maximum, minimum,
                 scanl, scanl1, scanr, scanr1, iterate, repeat, replicate, cycle,
                 take, drop, splitAt, takeWhile, dropWhile, span, break,
                 elem, notElem, lookup, zip, zip3, zipWith, zipWith3, unzip, unzip3,
                 lines, words, unlines, unwords)
import Data.Maybe(Maybe(..), maybe)
import Data.Monoid(Monoid(..))
import Data.Num(Num(..), subtract)
import Data.Ord(Ord(..), Ordering(..))
import Data.Ratio(Rational)
import Data.Real(Real(..))
import Data.Records  -- needed for data types with fields
import Data.String(IsString(..), lines, unlines, words, unwords)
import Data.Tuple(fst, snd, curry, uncurry)
import Data.Word(Word)
import System.IO(IO, putChar, putStr, putStrLn, print, getLine, getContents, interact,
                 FilePath, readFile, writeFile, appendFile,
                 cprint, cuprint)
import Text.Show(Show(..), ShowS, shows, showChar, showString, showParen)
import Primitives(_wordSize, _isWindows)
import Data.Text(Text)

-- So we can detect mhs vs ghc
usingMhs :: Bool
usingMhs = True

-------

appendDot :: Text -> Text -> Text
appendDot x y =
  _primitive "bs++." x y
  --x `append` pack "." `append` y

-- Exported by the runtime system to indicate if GMP is desired.
foreign import capi "want_gmp" want_gmp :: Int

wantGMP :: Bool
wantGMP = want_gmp /= 0

compiledWithMhs :: Bool
compiledWithMhs = True

instance NFData (a -> b) where
  rnf f = seq f ()

first :: forall a b c . (a -> c) -> (a, b) -> (c, b)
first f (a, b) = (f a, b)

second :: forall a b c . (b -> c) -> (a, b) -> (a, c)
second f (a, b) = (a, f b)
