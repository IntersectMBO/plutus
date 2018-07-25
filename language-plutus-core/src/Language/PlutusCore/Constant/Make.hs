{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RankNTypes        #-}
module Language.PlutusCore.Constant.Make
    ( makeBuiltinInt
    , makeBuiltinBS
    , makeBuiltinSize
    , makeBuiltinBool
    ) where

import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Constant.Prelude

import qualified Data.ByteString.Lazy as BSL

checkBoundsInt :: Size -> Integer -> Bool
checkBoundsInt s i = -2 ^ p <= i && i < 2 ^ p where
    p = 8 * fromIntegral s - 1 :: Int

checkBoundsBS :: Size -> BSL.ByteString -> Bool
checkBoundsBS = undefined

makeBuiltinInt :: Size -> Integer -> Maybe (Term TyName Name ())
makeBuiltinInt size int
    | checkBoundsInt size int = Just . Constant () $ BuiltinInt () size int
    | otherwise               = Nothing

makeBuiltinBS :: Size -> BSL.ByteString -> Maybe (Term TyName Name ())
makeBuiltinBS size bs
    | checkBoundsBS size bs = Just . Constant () $ BuiltinBS () size bs
    | otherwise             = Nothing

makeBuiltinSize :: Size -> Size -> Maybe (Term TyName Name ())
makeBuiltinSize size size'
    | size == size' = Just . Constant () $ BuiltinSize () size
    | otherwise     = Nothing

makeBuiltinBool :: Bool -> Maybe (Term TyName Name ())
makeBuiltinBool b = Just $ if b then builtinTrue else builtinFalse
