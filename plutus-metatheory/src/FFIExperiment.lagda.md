---
title: FFIExperiment
layout: page
---
```
module FFIExperiment where
```

## Imports

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)

```

## Less than or equal
```
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
```

## Nat example
```
¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)

```

## Compiler certification component
```

postulate
  something : {X : Set} → List (X ⊢) → Dec (X ⊢)

parseASTs : {X : Set} → List Untyped → List (Maybe X ⊢)
parseASTs [] = [] 
parseASTs (x ∷ xs) with toWellScoped x 
...        | inj₁ _ = [] 
...        | inj₂ t = t ∷ parseASTs xs

test : {X : Set} → List Untyped → Dec (Maybe X ⊢)
test us = something (parseASTs us)

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

runCertifier : List Untyped → IO ⊤
runCertifier us = putStrLn "TODO"
{-# COMPILE GHC runCertifier as runCertifier #-}
