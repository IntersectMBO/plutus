-- | Functions that generate Plutus Core terms from Haskell values and vice versa.

{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.StdLib.Meta
    ( metaIntegerToNat
    , metaEitherToSum
    , metaListToList
    ) where

import           PlutusCore.Core
import           PlutusCore.MkPlc
import           PlutusCore.Name

import           PlutusCore.StdLib.Data.List
import           PlutusCore.StdLib.Data.Nat  as Plc
import           PlutusCore.StdLib.Data.Sum

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
metaIntegerToNat :: TermLike term TyName Name uni fun => Integer -> term ()
metaIntegerToNat n
    | n < 0     = Prelude.error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = zero
          go m = apply () Plc.succ $ go (m - 1)

-- | Convert a Haskell 'Either' to a PLC @sum@.
metaEitherToSum
    :: TermLike term TyName Name uni fun
    => Type TyName uni ()
    -> Type TyName uni ()
    -> Either (term ()) (term ())
    -> term ()
metaEitherToSum a b (Left  x) = apply () (mkIterInst () left  [a, b]) x
metaEitherToSum a b (Right y) = apply () (mkIterInst () right [a, b]) y

-- | Convert a Haskell list of 'Term's to a PLC @list@.
metaListToList :: TermLike term TyName Name uni fun => Type TyName uni () -> [term ()] -> term ()
metaListToList ty =
    foldr
        (\x xs -> mkIterApp () (tyInst () cons ty) [x, xs])
        (tyInst () nil ty)
