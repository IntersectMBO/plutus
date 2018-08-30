{-# LANGUAGE GADTs #-}
module Language.PlutusCore.Constant.Make
    ( toBoundsInt
    , makeConstant
    ) where

import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

import qualified Data.ByteString.Lazy                 as BSL

-- | Return the @[-2^(8s - 1), 2^(8s - 1))@ bounds for integers of a given 'Size'.
toBoundsInt :: Size -> (Integer, Integer)
toBoundsInt s = (-2 ^ p, 2 ^ p) where
    p = 8 * fromIntegral s - 1 :: Int

-- | Check whether an 'Integer' is in the @[-2^(8s - 1), 2^(8s - 1))@ interval.
checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = low <= i && i < high where
    (low, high) = toBoundsInt s

-- | Check whether the length of a 'ByteString' is less than or equal to a given 'Size'.
checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS size bs = BSL.length bs <= fromIntegral size

-- | Check whether a 'Size' is a singleton.
checkBoundsSize :: Size -> Size -> Bool
checkBoundsSize = (==)

-- | Check whether an 'Integer' is in bounds (see 'checkBoundsInt') and return it as a 'Constant'.
makeBuiltinInt :: Size -> Integer -> Maybe (Constant ())
makeBuiltinInt size int = checkBoundsInt size int ? BuiltinInt () size int

-- | Check whether a 'ByteString' is in bounds (see 'checkBoundsBS') and return it as a 'Constant'.
makeBuiltinBS :: Size -> BSL.ByteString -> Maybe (Constant ())
makeBuiltinBS size bs = checkBoundsBS size bs ? BuiltinBS () size bs

-- | Check whether a 'Size' is a singleton and return it as a 'Constant'.
makeBuiltinSize :: Size -> Size -> Maybe (Constant ())
makeBuiltinSize size size' = checkBoundsSize size size' ? BuiltinSize () size

-- | Coerce a 'Bool' to the corresponding PLC's @boolean@.
makeDupBuiltinBool :: Bool -> Value TyName Name ()
makeDupBuiltinBool b = runQuote $ if b then getBuiltinTrue else getBuiltinFalse

-- | Coerce a Haskell value to the corresponding PLC constant indexed by size
-- checking all constraints (e.g. an 'Integer' is in appropriate bounds) along the way.
makeSizedConstant :: Size -> TypedBuiltinSized a -> a -> Maybe (Constant ())
makeSizedConstant size TypedBuiltinSizedInt  int   = makeBuiltinInt  size int
makeSizedConstant size TypedBuiltinSizedBS   bs    = makeBuiltinBS   size bs
makeSizedConstant size TypedBuiltinSizedSize size' = makeBuiltinSize size size'

-- | Coerce a Haskell value to the corresponding PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way.
makeConstant :: TypedBuiltin Size a -> a -> Maybe (Value TyName Name ())
makeConstant (TypedBuiltinSized se tbs) x =
    Constant () <$> makeSizedConstant (flattenSizeEntry se) tbs x
makeConstant TypedBuiltinBool           b = Just $ makeDupBuiltinBool b
