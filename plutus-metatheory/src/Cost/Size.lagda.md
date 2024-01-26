# Size of Constants

```
module Cost.Size where 

```

# Imports

```
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_)
open import Data.Nat.DivMod using (_/_)
open import Data.Integer using (ℤ;∣_∣)
open import Data.String using (length)

open import Utils using (_×_;_,_;_∷_;[];DATA;List;ByteString)
open DATA

open import Builtin using (lengthBS)
open import Builtin.Signature using (_⊢♯)
open _⊢♯

open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon
open import Cost.Base 
open import Untyped.CEK using (Value;V-con)
open import RawU using (TmCon;tmCon) 

open import Data.Vec using (Vec;[];_∷_) 
                     renaming (lookup to lookupVec)

```

## Memory usage of type constants

For each type constant we calculate its size, as a measure of memory usage.

First we bring some functions from Haskell world.

```
postulate ℕtoWords : ℤ → CostingNat 
postulate g1ElementCost : CostingNat
postulate g2ElementCost : CostingNat
postulate mlResultElementCost : CostingNat 

{-# FOREIGN GHC {-# LANGUAGE MagicHash #-} #-}
{-# FOREIGN GHC import GHC.Exts (Int (I#)) #-}
{-# FOREIGN GHC import GHC.Integer  #-}
{-# FOREIGN GHC import GHC.Integer.Logarithms  #-}
{-# FOREIGN GHC import GHC.Prim #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G1 as BLS12_381.G1 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G2 as BLS12_381.G2 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.Pairing as BLS12_381.Pairing #-}

{-# COMPILE GHC ℕtoWords = \i -> if i == 0 then 1 else fromIntegral $ I# (integerLog2# (abs i) `quotInt#` integerToInt 64) + 1 #-}
{-# COMPILE GHC g1ElementCost = toInteger (BLS12_381.G1.memSizeBytes `div` 8) #-}
{-# COMPILE GHC g2ElementCost = toInteger (BLS12_381.G2.memSizeBytes `div` 8) #-}
{-# COMPILE GHC mlResultElementCost = toInteger (BLS12_381.Pairing.mlResultMemSizeBytes `div` 8) #-}
```

For each constant we return the corresponding size.

```
byteStringSize : ByteString → CostingNat 
byteStringSize x = let n = ∣ lengthBS x ∣ in ((n ∸ 1) / 8) + 1

-- cost of a Data node
dataNodeMem : CostingNat 
dataNodeMem = 4

sizeData : DATA → CostingNat 
sizeDataList : List DATA → CostingNat 
sizeDataDataList : List (DATA × DATA) → CostingNat

sizeData (ConstrDATA _ xs) = dataNodeMem + sizeDataList xs
sizeData (MapDATA []) = dataNodeMem
sizeData (MapDATA xs) = dataNodeMem + sizeDataDataList xs
sizeData (ListDATA xs) = dataNodeMem + sizeDataList xs
sizeData (iDATA x) = dataNodeMem +  ℕtoWords x
sizeData (bDATA x) = dataNodeMem + byteStringSize x 

-- The following two functions are stupid but
-- they make the termination checker happy
sizeDataDataList [] = 0
sizeDataDataList ((x , y) ∷ xs) = sizeData x + sizeData y + sizeDataDataList xs

sizeDataList [] = 0
sizeDataList (x ∷ xs) = sizeData x + sizeDataList xs

defaultConstantMeasure : TmCon → CostingNat
defaultConstantMeasure (tmCon (atomic aInteger) x) = ℕtoWords x
defaultConstantMeasure (tmCon (atomic aBytestring) x) = byteStringSize x
defaultConstantMeasure (tmCon (atomic aString) x) = length x -- each Char costs 1
defaultConstantMeasure (tmCon (atomic aUnit) x) = 1
defaultConstantMeasure (tmCon (atomic aBool) x) = 1
defaultConstantMeasure (tmCon (atomic aData) d) = sizeData d
defaultConstantMeasure (tmCon (atomic aBls12-381-g1-element) x) = g1ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-g2-element) x) = g2ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-mlresult) x) = mlResultElementCost
defaultConstantMeasure (tmCon (list t) []) = 0
defaultConstantMeasure (tmCon (list t) (x ∷ xs)) = 
       defaultConstantMeasure (tmCon t x) 
     + defaultConstantMeasure (tmCon (list t) xs)
defaultConstantMeasure (tmCon (pair t u) (x , y)) = 
      1 + defaultConstantMeasure (tmCon t x) 
        + defaultConstantMeasure (tmCon u y)

-- This is the main sizing function for Values
-- It only measures constants. Other types should use models where the size 
-- of the non-constant does not matter.
defaultValueMeasure : Value → CostingNat 
defaultValueMeasure (V-con ty x) = defaultConstantMeasure (tmCon ty x)
defaultValueMeasure _ = 0
```