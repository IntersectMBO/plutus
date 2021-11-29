{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Size
    ( termSize
    , programSize
    , serialisedSize
    ) where

import UntypedPlutusCore.Core

import Data.ByteString qualified as BS
import Flat

-- | Count the number of AST nodes in a term.
termSize :: Term name uni fun ann -> Integer
termSize = \case
    Var{}         -> 1
    Delay _ t     -> 1 + termSize t
    Apply _ t t'  -> 1 + termSize t + termSize t'
    LamAbs _ _ t  -> 1 + termSize t
    Constant{}    -> 1
    Builtin{}     -> 1
    Force _ t     -> 1 + termSize t
    Constr _ _ es -> 1 + sum (fmap termSize es)
    Case _ arg cs -> 1 + termSize arg + sum (fmap termSize cs)
    Error _       -> 1

-- | Count the number of AST nodes in a program.
programSize :: Program name uni fun ann -> Integer
programSize (Program _ _ t) = termSize t

-- | Compute the size of the serialized form of a value.
serialisedSize :: Flat a => a -> Integer
serialisedSize = fromIntegral . BS.length . flat
