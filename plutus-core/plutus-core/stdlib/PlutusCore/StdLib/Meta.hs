{-# LANGUAGE OverloadedStrings #-}

-- | Functions that generate Plutus Core terms from Haskell values and vice versa.
module PlutusCore.StdLib.Meta
  ( metaIntegerToNat
  , metaEitherToSum
  , metaListToScottList
  ) where

import PlutusCore.Core
import PlutusCore.MkPlc
import PlutusCore.Name.Unique

import PlutusCore.StdLib.Data.Nat as Plc
import PlutusCore.StdLib.Data.ScottList
import PlutusCore.StdLib.Data.Sum

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
metaIntegerToNat :: TermLike term TyName Name uni fun => Integer -> term ()
metaIntegerToNat n
  | n < 0 = Prelude.error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
  | otherwise = go n
  where
    go 0 = zero
    go m = apply () Plc.succ $ go (m - 1)

-- | Convert a Haskell 'Either' to a PLC @sum@.
metaEitherToSum
  :: TermLike term TyName Name uni fun
  => Type TyName uni ()
  -> Type TyName uni ()
  -> Either (term ()) (term ())
  -> term ()
metaEitherToSum a b (Left x) = apply () (mkIterInstNoAnn left [a, b]) x
metaEitherToSum a b (Right y) = apply () (mkIterInstNoAnn right [a, b]) y

-- | Convert a Haskell list of 'Term's to a PLC @list@.
metaListToScottList
  :: TermLike term TyName Name uni fun => Type TyName uni () -> [term ()] -> term ()
metaListToScottList ty =
  foldr
    (\x xs -> mkIterAppNoAnn (tyInst () cons ty) [x, xs])
    (tyInst () nil ty)
