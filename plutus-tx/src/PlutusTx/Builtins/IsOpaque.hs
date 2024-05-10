{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeSynonymInstances     #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Builtins.IsOpaque where

import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing (MlResult)
import PlutusTx.Base (id, ($))
import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal

import Data.Kind qualified as GHC

type HasFromOpaque :: GHC.Type -> GHC.Constraint
class HasFromOpaque a where
    type FromOpaque a
    fromOpaque :: a -> FromOpaque a
class HasToOpaque a where
    toOpaque :: FromOpaque a -> a

instance HasFromOpaque BuiltinInteger where
    type FromOpaque BuiltinInteger = BuiltinInteger
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
instance HasToOpaque BuiltinInteger where
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance HasFromOpaque BuiltinByteString where
    type FromOpaque BuiltinByteString = BuiltinByteString
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
instance HasToOpaque BuiltinByteString where
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance HasFromOpaque BuiltinString where
    type FromOpaque BuiltinString = BuiltinString
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
instance HasToOpaque BuiltinString where
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance HasFromOpaque BuiltinUnit where
    type FromOpaque BuiltinUnit = ()
    {-# INLINABLE fromOpaque #-}
    fromOpaque u = chooseUnit u ()
instance HasToOpaque BuiltinUnit where
    {-# INLINABLE toOpaque #-}
    toOpaque x = case x of () -> unitval

instance HasFromOpaque BuiltinBool where
    type FromOpaque BuiltinBool = Bool
    {-# INLINABLE fromOpaque #-}
    fromOpaque b = ifThenElse b True False
instance HasToOpaque BuiltinBool where
    {-# INLINABLE toOpaque #-}
    toOpaque b = if b then true else false

instance HasFromOpaque a => HasFromOpaque (BuiltinList a) where
    type FromOpaque (BuiltinList a) = [FromOpaque a]

    {-# INLINABLE fromOpaque #-}
    fromOpaque = go
      where
          -- The combination of both INLINABLE and a type signature seems to stop this getting
          -- lifted to the top level, which means it gets a proper unfolding, which means that
          -- specialization can work, which can actually help quite a bit here.
          {-# INLINABLE go #-}
          go :: BuiltinList a -> [FromOpaque a]
          -- Note that we are using builtin chooseList here so this is *strict* application! So we
          -- need to do the manual laziness ourselves.
          go l = chooseList l (\_ -> []) (\_ -> fromOpaque (head l) : go (tail l)) unitval

instance HasToOpaque (BuiltinList BuiltinData) where
    {-# INLINE toOpaque #-}
    toOpaque = goList where
        goList :: [BuiltinData] -> BuiltinList BuiltinData
        goList []     = mkNilData unitval
        goList (d:ds) = mkCons (toOpaque d) (goList ds)

instance HasToOpaque (BuiltinList (BuiltinPair BuiltinData BuiltinData)) where
    {-# INLINE toOpaque #-}
    toOpaque = goList where
        goList :: [(BuiltinData, BuiltinData)] -> BuiltinList (BuiltinPair BuiltinData BuiltinData)
        goList []     = mkNilPairData unitval
        goList (d:ds) = mkCons (toOpaque d) (goList ds)

instance (HasFromOpaque a, HasFromOpaque b) => HasFromOpaque (BuiltinPair a b) where
    type FromOpaque (BuiltinPair a b) = (FromOpaque a, FromOpaque b)
    {-# INLINABLE fromOpaque #-}
    fromOpaque p = (fromOpaque $ fst p, fromOpaque $ snd p)
instance HasToOpaque (BuiltinPair BuiltinData BuiltinData) where
    {-# INLINABLE toOpaque #-}
    toOpaque (d1, d2) = mkPairData d1 d2

instance HasFromOpaque BuiltinData where
    type FromOpaque BuiltinData = BuiltinData
    {-# INLINABLE fromOpaque #-}
    fromOpaque = id
instance HasToOpaque BuiltinData where
    {-# INLINABLE toOpaque #-}
    toOpaque = id

instance HasFromOpaque BuiltinBLS12_381_G1_Element where
    type FromOpaque BuiltinBLS12_381_G1_Element = BLS12_381.G1.Element
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_G1_Element a) = a
instance HasToOpaque BuiltinBLS12_381_G1_Element where
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_G1_Element

instance HasFromOpaque BuiltinBLS12_381_G2_Element where
    type FromOpaque BuiltinBLS12_381_G2_Element = BLS12_381.G2.Element
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_G2_Element a) = a
instance HasToOpaque BuiltinBLS12_381_G2_Element where
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_G2_Element

instance HasFromOpaque BuiltinBLS12_381_MlResult where
    type FromOpaque BuiltinBLS12_381_MlResult = BLS12_381.Pairing.MlResult
    {-# INLINABLE fromOpaque #-}
    fromOpaque (BuiltinBLS12_381_MlResult a) = a
instance HasToOpaque BuiltinBLS12_381_MlResult where
    {-# INLINABLE toOpaque #-}
    toOpaque = BuiltinBLS12_381_MlResult
