{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
module Language.PlutusCore.Constant.Make
    ( makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinSize
    , makeDupBuiltinBool
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Constant.Prelude

import qualified Data.ByteString.Lazy as BSL

-- | Check whether an 'Integer' is in the @[-2^(8s - 1), 2^(8s - 1))@ interval.
checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = -2 ^ p <= i && i < 2 ^ p where
    p = 8 * fromIntegral s - 1 :: Int

checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS = undefined

-- | Check whether an 'Integer' is in bounds (see 'checkBoundsInt') and return it as a term.
makeBuiltinInt :: Size -> Integer -> Maybe (Term TyName Name ())
makeBuiltinInt size int = checkBoundsInt size int ? Constant () (BuiltinInt () size int)

-- | Check whether a 'ByteString' is in bounds (see 'checkBoundsBS') and return it as a term.
makeBuiltinBS :: Size -> BSL.ByteString -> Maybe (Term TyName Name ())
makeBuiltinBS size bs = checkBoundsBS size bs ? Constant () (BuiltinBS () size bs)

-- | Check whether a 'Size' is a singleton and return it as a term.
makeBuiltinSize :: Size -> Size -> Maybe (Term TyName Name ())
makeBuiltinSize size size' = size == size' ? Constant () (BuiltinSize () size)

-- | Coerce a 'Bool' to PLC's @boolean@.
makeDupBuiltinBool :: Bool -> Term TyName Name ()
makeDupBuiltinBool b = dropFresh $ if b then getBuiltinTrue else getBuiltinFalse
