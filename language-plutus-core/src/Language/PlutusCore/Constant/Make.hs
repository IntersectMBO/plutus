-- | Smart constructors of PLC constants.

{-# LANGUAGE GADTs #-}
module Language.PlutusCore.Constant.Make
    ( toBoundsInt
    , makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinSize
    , makeBuiltinBool
    , makeSizedConstant
    , makeBuiltin
    , unsafeMakeBuiltin
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.StdLib.Data.Bool

import           Data.Maybe
import qualified Data.ByteString.Lazy as BSL

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

-- | Convert a 'Bool' to the corresponding PLC's @boolean@.
makeBuiltinBool :: Bool -> Quote (Value TyName Name ())
makeBuiltinBool b = if b then getBuiltinTrue else getBuiltinFalse

-- | Convert a Haskell value to the corresponding PLC constant indexed by size
-- checking all constraints (e.g. an 'Integer' is in appropriate bounds) along the way.
makeSizedConstant :: Size -> TypedBuiltinSized a -> a -> Maybe (Constant ())
makeSizedConstant size TypedBuiltinSizedInt  int   = makeBuiltinInt  size int
makeSizedConstant size TypedBuiltinSizedBS   bs    = makeBuiltinBS   size bs
makeSizedConstant size TypedBuiltinSizedSize size' = makeBuiltinSize size size'

-- | Convert a Haskell value to the corresponding PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way.
-- Does not preserve the global uniqueness condition.
makeBuiltin :: TypedBuiltinValue Size a -> Quote (Maybe (Value TyName Name ()))
makeBuiltin (TypedBuiltinValue tb x) = case tb of
    (TypedBuiltinSized se tbs) ->
        return $ Constant () <$> makeSizedConstant (flattenSizeEntry se) tbs x
    TypedBuiltinBool           -> Just <$> makeBuiltinBool x

-- | Convert a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
-- Does not preserve the global uniqueness condition.
unsafeMakeBuiltin :: TypedBuiltinValue Size a -> Value TyName Name ()
unsafeMakeBuiltin tbv = fromMaybe err . runQuote $ makeBuiltin tbv where
    err = error $ "unsafeDupMakeConstant: out of bounds: " ++ prettyString tbv
