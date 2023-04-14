
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

We have six base types referred to as atomic type constants:

```
data AtomicTyCon : Set where
  aInteger    : AtomicTyCon
  aBytestring : AtomicTyCon 
  aString     : AtomicTyCon 
  aUnit       : AtomicTyCon 
  aBool       : AtomicTyCon
  aData       : AtomicTyCon 

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC AtomicTyCon = data AtomicTyCon (ATyConInt | ATyConBS | ATyConStr | ATyConUnit | ATyConBool | ATyConData) #-}

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
decAtomicTyCon aBytestring aInteger = no λ()
decAtomicTyCon aBytestring aBytestring = yes refl
decAtomicTyCon aBytestring aString = no λ()
decAtomicTyCon aBytestring aUnit = no λ()
decAtomicTyCon aBytestring aBool = no λ()
decAtomicTyCon aBytestring aData = no λ()
decAtomicTyCon aString aInteger = no λ()
decAtomicTyCon aString aBytestring = no λ()
decAtomicTyCon aString aString = yes refl
decAtomicTyCon aString aUnit = no λ()
decAtomicTyCon aString aBool = no λ()
decAtomicTyCon aString aData = no λ()
decAtomicTyCon aUnit aInteger = no λ()
decAtomicTyCon aUnit aBytestring = no λ()
decAtomicTyCon aUnit aString = no λ()
decAtomicTyCon aUnit aUnit = yes refl
decAtomicTyCon aUnit aBool = no λ()
decAtomicTyCon aUnit aData = no λ()
decAtomicTyCon aBool aInteger = no λ()
decAtomicTyCon aBool aBytestring = no λ()
decAtomicTyCon aBool aString = no λ()
decAtomicTyCon aBool aUnit = no λ()
decAtomicTyCon aBool aBool = yes refl
decAtomicTyCon aBool aData = no λ()
decAtomicTyCon aData aInteger = no λ()
decAtomicTyCon aData aBytestring = no λ()
decAtomicTyCon aData aString = no λ()
decAtomicTyCon aData aUnit = no λ()
decAtomicTyCon aData aBool = no λ()
decAtomicTyCon aData aData = yes refl
```
