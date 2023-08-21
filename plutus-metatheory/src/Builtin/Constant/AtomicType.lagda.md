
```
module Builtin.Constant.AtomicType where
```

## Imports

```
open import Data.Bool using (Bool)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Relation.Binary using (DecidableEquality)

open import Utils using (ByteString;DATA;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult)
open import Utils.Reflection using (defDec)

```

# Atomic Type constants

We have nine base types referred to as atomic type constants:

```
data AtomicTyCon : Set where
  aInteger              : AtomicTyCon
  aBytestring           : AtomicTyCon 
  aString               : AtomicTyCon 
  aUnit                 : AtomicTyCon 
  aBool                 : AtomicTyCon
  aData                 : AtomicTyCon 
  aBls12-381-g1-element : AtomicTyCon
  aBls12-381-g2-element : AtomicTyCon
  aBls12-381-mlresult   : AtomicTyCon

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC AtomicTyCon = data AtomicTyCon (ATyConInt | ATyConBS | ATyConStr | ATyConUnit | ATyConBool | ATyConData | ATyConBLS12_381_G1_Element | ATyConBLS12_381_G2_Element | ATyConBLS12_381_MlResult) #-}

```

## Decidable Equality of `AtomicTyCon`.

```
decAtomicTyCon : DecidableEquality AtomicTyCon
unquoteDef decAtomicTyCon = defDec (quote AtomicTyCon) decAtomicTyCon
```

## Meaning of Atomic Constants

```
⟦_⟧at : AtomicTyCon → Set
⟦ aInteger ⟧at = ℤ
⟦ aBytestring ⟧at = ByteString
⟦ aString ⟧at = String
⟦ aUnit ⟧at = ⊤
⟦ aBool ⟧at = Bool
⟦ aData ⟧at = DATA
⟦ aBls12-381-g1-element ⟧at = Bls12-381-G1-Element
⟦ aBls12-381-g2-element ⟧at = Bls12-381-G2-Element
⟦ aBls12-381-mlresult ⟧at = Bls12-381-MlResult

