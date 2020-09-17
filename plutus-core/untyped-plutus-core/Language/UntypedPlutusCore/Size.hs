{-# LANGUAGE LambdaCase #-}

module Language.UntypedPlutusCore.Size
    ( termSize
    , programSize
    , serialisedSize
    ) where

import           Language.UntypedPlutusCore.Core

import           Codec.Serialise
import qualified Data.ByteString.Lazy            as BSL

-- | Count the number of AST nodes in a term.
termSize :: Term name uni fun ann -> Integer
termSize = \case
    Var{} -> 1
    Delay _ t -> 1 + termSize t
    Apply _ t t' -> 1 + termSize t + termSize t'
    LamAbs _ _ t -> 1 + termSize t
    Constant{} -> 1
    Builtin{} -> 1
    Force _ t -> 1 + termSize t
    Error _ -> 1

-- | Count the number of AST nodes in a program.
programSize :: Program name uni fun ann -> Integer
programSize (Program _ _ t) = termSize t

-- | Compute the size of the serializabled form of a value.
serialisedSize :: Serialise a => a -> Integer
serialisedSize = fromIntegral . BSL.length . serialise
