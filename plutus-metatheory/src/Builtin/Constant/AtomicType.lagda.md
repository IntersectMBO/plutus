
```
module Builtin.Constant.AtomicType where
```

## Imports

```
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (yes;no;¬_)
open import Relation.Binary.PropositionalEquality using (refl)
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
decAtomicTyCon aInteger aInteger = yes refl
decAtomicTyCon aInteger aBytestring = no λ()
decAtomicTyCon aInteger aString = no λ()
decAtomicTyCon aInteger aUnit = no λ()
decAtomicTyCon aInteger aBool = no λ()
decAtomicTyCon aInteger aData = no λ()
decAtomicTyCon aInteger aBls12-381-g1-element = no λ()
decAtomicTyCon aInteger aBls12-381-g2-element = no λ()
decAtomicTyCon aInteger aBls12-381-mlresult = no λ()
decAtomicTyCon aBytestring aInteger = no λ()
decAtomicTyCon aBytestring aBytestring = yes refl
decAtomicTyCon aBytestring aString = no λ()
decAtomicTyCon aBytestring aUnit = no λ()
decAtomicTyCon aBytestring aBool = no λ()
decAtomicTyCon aBytestring aData = no λ()
decAtomicTyCon aBytestring aBls12-381-g1-element = no λ()
decAtomicTyCon aBytestring aBls12-381-g2-element = no λ()
decAtomicTyCon aBytestring aBls12-381-mlresult = no λ()
decAtomicTyCon aString aInteger = no λ()
decAtomicTyCon aString aBytestring = no λ()
decAtomicTyCon aString aString = yes refl
decAtomicTyCon aString aUnit = no λ()
decAtomicTyCon aString aBool = no λ()
decAtomicTyCon aString aData = no λ()
decAtomicTyCon aString aBls12-381-g1-element = no λ()
decAtomicTyCon aString aBls12-381-g2-element = no λ()
decAtomicTyCon aString aBls12-381-mlresult = no λ()
decAtomicTyCon aUnit aInteger = no λ()
decAtomicTyCon aUnit aBytestring = no λ()
decAtomicTyCon aUnit aString = no λ()
decAtomicTyCon aUnit aUnit = yes refl
decAtomicTyCon aUnit aBool = no λ()
decAtomicTyCon aUnit aData = no λ()
decAtomicTyCon aUnit aBls12-381-g1-element = no λ()
decAtomicTyCon aUnit aBls12-381-g2-element = no λ()
decAtomicTyCon aUnit aBls12-381-mlresult = no λ()
decAtomicTyCon aBool aInteger = no λ()
decAtomicTyCon aBool aBytestring = no λ()
decAtomicTyCon aBool aString = no λ()
decAtomicTyCon aBool aUnit = no λ()
decAtomicTyCon aBool aBool = yes refl
decAtomicTyCon aBool aData = no λ()
decAtomicTyCon aBool aBls12-381-g1-element = no λ()
decAtomicTyCon aBool aBls12-381-g2-element = no λ()
decAtomicTyCon aBool aBls12-381-mlresult = no λ()
decAtomicTyCon aData aInteger = no λ()
decAtomicTyCon aData aBytestring = no λ()
decAtomicTyCon aData aString = no λ()
decAtomicTyCon aData aUnit = no λ()
decAtomicTyCon aData aBool = no λ()
decAtomicTyCon aData aData = yes refl
decAtomicTyCon aData aBls12-381-g1-element = no λ()
decAtomicTyCon aData aBls12-381-g2-element = no λ()
decAtomicTyCon aData aBls12-381-mlresult = no λ()
decAtomicTyCon aBls12-381-g1-element aInteger = no λ()
decAtomicTyCon aBls12-381-g1-element aBytestring = no λ()
decAtomicTyCon aBls12-381-g1-element aString = no λ()
decAtomicTyCon aBls12-381-g1-element aUnit = no λ()
decAtomicTyCon aBls12-381-g1-element aBool = no λ()
decAtomicTyCon aBls12-381-g1-element aData = no λ()
decAtomicTyCon aBls12-381-g1-element aBls12-381-g1-element = yes refl
decAtomicTyCon aBls12-381-g1-element aBls12-381-g2-element = no λ()
decAtomicTyCon aBls12-381-g1-element aBls12-381-mlresult = no λ()
decAtomicTyCon aBls12-381-g2-element aInteger = no λ()
decAtomicTyCon aBls12-381-g2-element aBytestring = no λ()
decAtomicTyCon aBls12-381-g2-element aString = no λ()
decAtomicTyCon aBls12-381-g2-element aUnit = no λ()
decAtomicTyCon aBls12-381-g2-element aBool = no λ()
decAtomicTyCon aBls12-381-g2-element aData = no λ()
decAtomicTyCon aBls12-381-g2-element aBls12-381-g1-element = no λ()
decAtomicTyCon aBls12-381-g2-element aBls12-381-g2-element = yes refl
decAtomicTyCon aBls12-381-g2-element aBls12-381-mlresult = no λ()
decAtomicTyCon aBls12-381-mlresult aInteger = no λ()
decAtomicTyCon aBls12-381-mlresult aBytestring = no λ()
decAtomicTyCon aBls12-381-mlresult aString = no λ()
decAtomicTyCon aBls12-381-mlresult aUnit = no λ()
decAtomicTyCon aBls12-381-mlresult aBool = no λ()
decAtomicTyCon aBls12-381-mlresult aData = no λ()
decAtomicTyCon aBls12-381-mlresult aBls12-381-g1-element = no λ()
decAtomicTyCon aBls12-381-mlresult aBls12-381-g2-element = no λ()
decAtomicTyCon aBls12-381-mlresult aBls12-381-mlresult = yes refl

```
