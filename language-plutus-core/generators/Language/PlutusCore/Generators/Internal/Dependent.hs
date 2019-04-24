-- | Orphan 'GEq' and 'GCompare' instances of data types from "Language.PlutusCore.Constant.Typed".
-- The reason we keep the instances separate is that they are highly unsafe ('unsafeCoerce' is used)
-- and needed only for tests.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Generators.Internal.Dependent () where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Pretty

import           Control.Monad
import           Data.GADT.Compare
import           Unsafe.Coerce

liftOrdering :: Ordering -> GOrdering a b
liftOrdering LT = GLT
liftOrdering EQ = error "'liftOrdering': 'Eq'"
liftOrdering GT = GGT

-- I tried using the 'dependent-sum-template' package,
-- but see https://stackoverflow.com/q/50048842/3237465
instance GEq TypedBuiltinSized where
    TypedBuiltinSizedInt  `geq` TypedBuiltinSizedInt  = Just Refl
    TypedBuiltinSizedBS   `geq` TypedBuiltinSizedBS   = Just Refl
    _                     `geq` _                     = Nothing

instance GEq TypedBuiltin where
    TypedBuiltinSized tbs1 `geq` TypedBuiltinSized tbs2 = tbs1 `geq` tbs2
    dyn1@TypedBuiltinDyn         `geq` dyn2@TypedBuiltinDyn         = do
        guard $ prettyString dyn1 == prettyString dyn2
        Just $ unsafeCoerce Refl
    _                            `geq` _                            = Nothing

instance GCompare TypedBuiltin where
    tb1                          `gcompare` tb2
        | Just Refl <- tb1  `geq` tb2  = GEQ
    TypedBuiltinSized tbs1 `gcompare` TypedBuiltinSized tbs2
        | Just Refl <- tbs1 `geq` tbs2 = GEQ
        | otherwise                    = case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , _                    ) -> GLT
            (TypedBuiltinSizedBS  , TypedBuiltinSizedInt ) -> GGT
            (TypedBuiltinSizedBS  , _                    ) -> GLT
    dyn1@TypedBuiltinDyn         `gcompare` dyn2@TypedBuiltinDyn
        = liftOrdering $ prettyString dyn1 `compare` prettyString dyn2
    TypedBuiltinSized _        `gcompare` TypedBuiltinDyn
        = GLT
    TypedBuiltinDyn              `gcompare` TypedBuiltinSized _
        = GGT
