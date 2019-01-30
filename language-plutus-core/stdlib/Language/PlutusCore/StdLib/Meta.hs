-- | Functions that generate Plutus Core terms from Haskell values and vice versa.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.StdLib.Meta
    ( metaIntegerToNat
    , metaEitherToSum
    , metaListToList
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type

import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat  as Plc
import           Language.PlutusCore.StdLib.Data.Sum

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
metaIntegerToNat :: Integer -> Term TyName Name ()
metaIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = zero
          go m = Apply () Plc.succ $ go (m - 1)

-- | Convert a Haskell 'Either' to a PLC @sum@.
metaEitherToSum
    :: Type TyName ()
    -> Type TyName ()
    -> Either (Term TyName Name ()) (Term TyName Name ())
    -> Term TyName Name ()
metaEitherToSum a b (Left  x) = Apply () (mkIterInst () left  [a, b]) x
metaEitherToSum a b (Right y) = Apply () (mkIterInst () right [a, b]) y

-- | Convert a Haskell list of 'Term's to a PLC @list@.
metaListToList :: Type TyName () -> [Term TyName Name ()] -> Term TyName Name ()
metaListToList ty =
    foldr
        (\x xs -> mkIterApp () (TyInst () cons ty) [x, xs])
        (TyInst () nil ty)
