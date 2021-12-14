-- |
-- Module      : Foundation
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- I tried to picture clusters of information
-- As they moved through the computer
-- What do they look like?
--
-- Alternative Prelude
module Foundation
    ( -- * Standard
      -- ** Operators
      (Prelude.$)
    , (Prelude.$!)
    , (Prelude.&&)
    , (Prelude.||)
    , (Control.Category..)
      -- ** Functions
    , Prelude.not
    , Prelude.otherwise
    , module Foundation.Tuple
    , Control.Category.id
    , Prelude.maybe
    , Prelude.either
    , Prelude.flip
    , Prelude.const
    , Basement.Imports.error
    , Foundation.IO.Terminal.putStr
    , Foundation.IO.Terminal.putStrLn
    --, print
    , getArgs
    , Prelude.uncurry
    , Prelude.curry
    , Data.Tuple.swap
    , Prelude.until
    , Prelude.asTypeOf
    , Prelude.undefined
    , Prelude.seq
    , Foundation.Primitive.NormalForm
    , Foundation.Primitive.deepseq
    , Foundation.Primitive.force
      -- ** Type classes
    , Prelude.Show
    , Basement.Imports.show
    , Prelude.Ord (..)
    , Prelude.Eq (..)
    , Prelude.Bounded (..)
    , Prelude.Enum (..)
    , Prelude.Functor (..)
    , Integral (..)
    , Fractional (..)
    , HasNegation (..)
    , Basement.Compat.Bifunctor.Bifunctor (..)
    , Control.Applicative.Applicative (..)
    , Prelude.Monad (..)
    , (Control.Monad.=<<)
    --, Foundation.String.IsString (..)
    , IsString(..)
    , IsList(..)
      -- ** Numeric type classes
    , Foundation.Numerical.IsIntegral (..)
    , Foundation.Numerical.IsNatural (..)
    , Foundation.Numerical.Signed (..)
    , Foundation.Numerical.Additive (..)
    , Foundation.Numerical.Subtractive (..)
    , Foundation.Numerical.Multiplicative (..)
    , Foundation.Numerical.IDivisible(..)
    , Foundation.Numerical.Divisible(..)
      -- ** Data types
    , Prelude.Maybe (..)
    , Prelude.Ordering (..)
    , Prelude.Bool (..)
    , Prelude.Char
    , Char7
    , Prelude.IO
    , Prelude.Either (..)
      -- ** Numbers
    , Data.Int.Int8, Data.Int.Int16, Data.Int.Int32, Data.Int.Int64
    , Data.Word.Word8, Data.Word.Word16, Data.Word.Word32, Data.Word.Word64, Data.Word.Word
    , Word128, Word256
    , Prelude.Int
    , Prelude.Integer
    , Natural
    , Prelude.Rational
    , Prelude.Float
    , Prelude.Double
    , CountOf(..), Offset(..)
    , toCount
    , fromCount
      -- ** Collection types
    , UArray
    , PrimType
    , Array
    , String
      -- ** Numeric functions
    -- , (Prelude.^)
    , (Prelude.^^)
    , Prelude.fromIntegral
    , Prelude.realToFrac
      -- ** Monoids
    , Basement.Compat.Semigroup.Semigroup
    , Monoid (..)
    , (<>)
      -- ** Collection
    , Collection(..)
    , and
    , or
    , Sequential(..)
    , NonEmpty
    , nonEmpty
      -- ** Folds
    , Foldable(..)
      -- ** Maybe
    , Data.Maybe.mapMaybe
    , Data.Maybe.catMaybes
    , Data.Maybe.fromMaybe
    , Data.Maybe.isJust
    , Data.Maybe.isNothing
    , Data.Maybe.listToMaybe
    , Data.Maybe.maybeToList
      -- ** Either
    , Data.Either.partitionEithers
    , Data.Either.lefts
    , Data.Either.rights
      -- ** Function
    , Data.Function.on
      -- ** Applicative
    , (Control.Applicative.<$>)
    , (Control.Applicative.<|>)
      -- ** Monad
    , (Control.Monad.>=>)
      -- ** Exceptions
    , Control.Exception.Exception (..)
    , Data.Typeable.Typeable
    , Control.Exception.SomeException
    , Control.Exception.IOException
      -- ** Proxy
    , Data.Proxy.Proxy(..)
    , Data.Proxy.asProxyTypeOf
      -- ** Partial
    , Foundation.Partial.Partial
    , Foundation.Partial.partial
    , Foundation.Partial.PartialError
    , Foundation.Partial.fromPartial
    , Basement.Compat.Base.ifThenElse
      -- ** Old Prelude Strings as [Char] with bridge back and forth
    , LString
    ) where

import qualified Prelude
--import           Prelude (Char, (.), Eq, Bool, IO)

import           Data.Monoid (Monoid (..), (<>))
import           Control.Applicative
import qualified Control.Category
import qualified Control.Monad
import qualified Control.Exception
import qualified Data.Typeable

import           Data.Word (Word8, Word16, Word32, Word64, Word)
import           Data.Int (Int8, Int16, Int32, Int64)
import           Foundation.String (String)
import           Foundation.Array (UArray, Array, PrimType)
import           Foundation.Collection (Collection(..), and, or, Sequential(..)
                 , NonEmpty, nonEmpty, Foldable(..))
import qualified Foundation.IO.Terminal

import           GHC.Exts (IsString(..))
import           Basement.Compat.IsList
import qualified Basement.Compat.Base (ifThenElse)
import qualified Data.Proxy

import qualified Foundation.Numerical
import qualified Foundation.Partial
import           Foundation.Tuple

import qualified Basement.Compat.Bifunctor
import           Basement.Types.OffsetSize (CountOf(..), Offset(..))
import           Basement.Types.Word128 (Word128)
import           Basement.Types.Word256 (Word256)
import           Basement.Types.Char7 (Char7)
import qualified Foundation.Primitive
import qualified Basement.Imports
import           Basement.Environment (getArgs)
import           Basement.Compat.NumLiteral
import           Basement.Compat.Natural
import qualified Basement.Compat.Semigroup

import qualified Data.Maybe
import qualified Data.Either
import qualified Data.Function
import qualified Data.Tuple

default (Prelude.Integer, Prelude.Double)

-- | Alias to Prelude String ([Char]) for compatibility purpose
type LString = Prelude.String

fromCount :: CountOf ty -> Prelude.Int
fromCount (CountOf n) = n

toCount :: Prelude.Int -> CountOf ty
toCount i
    | i Prelude.<= 0    = CountOf 0
    | Prelude.otherwise = CountOf i
