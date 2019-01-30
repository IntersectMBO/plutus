-- | Functions that generate Plutus Core terms from Haskell values and vice versa.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Meta
    ( getBuiltinIntegerToNat
    , getEitherToBuiltinSum
    , getListToBuiltinList
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Sum

import           Data.Functor                         ((<&>))

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
getBuiltinIntegerToNat :: Integer -> Quote (Term TyName Name ())
getBuiltinIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = getBuiltinZero
          go m = Apply () <$> getBuiltinSucc <*> go (m - 1)

-- | Convert a Haskell 'Either' to a PLC @sum@.
getEitherToBuiltinSum
    :: Type TyName ()
    -> Type TyName ()
    -> Either (Term TyName Name ()) (Term TyName Name ())
    -> Quote (Term TyName Name ())
getEitherToBuiltinSum a b (Left  x) =
    getBuiltinLeft  <&> \left  -> Apply () (mkIterInst () left  [a, b]) x
getEitherToBuiltinSum a b (Right y) =
    getBuiltinRight <&> \right -> Apply () (mkIterInst () right [a, b]) y

-- | Convert a Haskell list of 'Term's to a PLC @list@.
getListToBuiltinList :: Type TyName () -> [Term TyName Name ()] -> Quote (Term TyName Name ())
getListToBuiltinList ty ts = rename =<< do
    builtinNil  <- getBuiltinNil
    builtinCons <- getBuiltinCons
    return $ foldr
        (\x xs -> mkIterApp () (TyInst () builtinCons ty) [x, xs])
        (TyInst () builtinNil ty)
        ts
