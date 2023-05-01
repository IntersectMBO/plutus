
```
module Builtin.Constant.AtomicType where
```

## Imports

```
open import Relation.Binary using (DecidableEquality)
open import Utils.Reflection using (defDec)
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
unquoteDef decAtomicTyCon = defDec (quote AtomicTyCon) decAtomicTyCon
```
