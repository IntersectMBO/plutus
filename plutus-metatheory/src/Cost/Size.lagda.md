---
title: Cost.Size
layout: page
---
# Size of Constants

```
module Cost.Size where

```

# Imports

```
open import Data.Bool using (Bool)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ;_+_)
open import Data.Integer using (ℤ)
open import Data.String using (String)

open import Utils using (_,_;_∷_;[];DATA;List;ByteString)
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon
open import Cost.Base
open import Untyped.CEK using (Value;V-con)
open import RawU using (TmCon;tmCon)
```

## Memory usage of type constants

For each type constant we calculate its size, as a measure of memory usage.

First we bring some functions from Haskell world.

```
postulate integerSize : ℤ → CostingNat
postulate byteStringSize : ByteString → CostingNat
postulate g1ElementSize : Utils.Bls12-381-G1-Element → CostingNat
postulate g2ElementSize : Utils.Bls12-381-G2-Element → CostingNat
postulate mlResultElementSize : Utils.Bls12-381-MlResult → CostingNat
postulate dataSize : DATA → CostingNat
postulate boolSize : Bool → CostingNat
postulate unitSize : ⊤ → CostingNat
postulate stringSize : String → CostingNat

{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExMemoryUsage #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.CostStream #-}
{-# FOREIGN GHC import Data.SatInt #-}
{-# FOREIGN GHC size = fromSatInt . sumCostStream . flattenCostRose . memoryUsage #-}
{-# COMPILE GHC integerSize = size  #-}
{-# COMPILE GHC byteStringSize = size  #-}
{-# COMPILE GHC g1ElementSize = size #-}
{-# COMPILE GHC g2ElementSize = size #-}
{-# COMPILE GHC mlResultElementSize = size #-}
{-# COMPILE GHC dataSize  = size #-}
{-# COMPILE GHC boolSize = size #-}
{-# COMPILE GHC unitSize = size #-}
{-# COMPILE GHC stringSize  = size #-}
```

For each constant we return the corresponding size.
These *must* match the size functions defined in
`PlutusCore.Evaluation.Machine.ExMemoryUsage`
```
defaultConstantMeasure : TmCon → CostingNat
defaultConstantMeasure (tmCon (atomic aInteger) x) = integerSize x
defaultConstantMeasure (tmCon (atomic aBytestring) x) = byteStringSize x
defaultConstantMeasure (tmCon (atomic aString) x) = stringSize x
defaultConstantMeasure (tmCon (atomic aUnit) x) = unitSize x
defaultConstantMeasure (tmCon (atomic aBool) x) = boolSize x
defaultConstantMeasure (tmCon (atomic aData) d) = dataSize d
defaultConstantMeasure (tmCon (atomic aBls12-381-g1-element) x) = g1ElementSize x
defaultConstantMeasure (tmCon (atomic aBls12-381-g2-element) x) = g2ElementSize x
defaultConstantMeasure (tmCon (atomic aBls12-381-mlresult) x) = mlResultElementSize x
defaultConstantMeasure (tmCon (list t) l) = Utils.length l
defaultConstantMeasure (tmCon (array t) a) with Utils.HSlengthOfArray a
... | ℤ.pos ℕ.zero = 1
... | ℤ.pos (ℕ.suc n) = ℕ.suc n
... | ℤ.negsuc n = 1
defaultConstantMeasure (tmCon (pair t u) (x , y)) = 1

-- This is the main sizing function for Values
-- It only measures constants. Other types should use models where the size
-- of the non-constant does not matter.
defaultValueMeasure : Value → CostingNat
defaultValueMeasure (V-con ty x) = defaultConstantMeasure (tmCon ty x)
defaultValueMeasure _ = 0
```
