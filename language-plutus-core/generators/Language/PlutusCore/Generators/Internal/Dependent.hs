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
    TypedBuiltinSizedSize `geq` TypedBuiltinSizedSize = Just Refl
    _                     `geq` _                     = Nothing

instance (Pretty size, Eq size) => GEq (TypedBuiltin size) where
    TypedBuiltinSized size1 tbs1 `geq` TypedBuiltinSized size2 tbs2 = do
        guard $ size1 == size2
        tbs1 `geq` tbs2
    dyn1@TypedBuiltinDyn         `geq` dyn2@TypedBuiltinDyn         = do
        guard $ prettyString dyn1 == prettyString dyn2
        Just $ unsafeCoerce Refl
    _                            `geq` _                            = Nothing

instance (Pretty size, Ord size) => GCompare (TypedBuiltin size) where
    tb1                          `gcompare` tb2
        | Just Refl <- tb1  `geq` tb2  = GEQ
    TypedBuiltinSized size1 tbs1 `gcompare` TypedBuiltinSized size2 tbs2
        | Just Refl <- tbs1 `geq` tbs2 = liftOrdering $ size1 `compare` size2
        | otherwise                    = case (tbs1, tbs2) of
            (TypedBuiltinSizedInt , _                    ) -> GLT
            (TypedBuiltinSizedBS  , TypedBuiltinSizedInt ) -> GGT
            (TypedBuiltinSizedBS  , _                    ) -> GLT
            (TypedBuiltinSizedSize, _                    ) -> GGT
    dyn1@TypedBuiltinDyn         `gcompare` dyn2@TypedBuiltinDyn
        = liftOrdering $ prettyString dyn1 `compare` prettyString dyn2
    TypedBuiltinSized _ _        `gcompare` TypedBuiltinDyn
        = GLT
    TypedBuiltinDyn              `gcompare` TypedBuiltinSized _ _
        = GGT
