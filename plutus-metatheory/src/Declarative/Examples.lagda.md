---
title: Declarative Term Examples
layout: page
---

This file contains some examples of plutus core terms such as Church
and Scott numerals and their respective addition operations.

```
module Declarative.Examples where
```

## Imports

```
open import Agda.Builtin.Int using (pos)
open import Relation.Binary.PropositionalEquality using (refl)

open import Type using (_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_
import Type.RenamingSubstitution as ⋆
open import Type.Equality using (β≡β)
open import Declarative using (Ctx;_⊢_;_∋_)
open Ctx
open _⊢_
open _∋_
open import Builtin using (addInteger)
open import Builtin.Constant.Type using (TyCon;aInteger)
open TyCon
open import Declarative.Examples.StdLib.Function using (unwrap0;Z-comb)
import Declarative.Examples.StdLib.ChurchNat using (inc;N;Succ;Zero;Iter)
open import Type.Equality using (_≡β_)
open _≡β_
```

## Examples

```
integer = atomic aInteger

module Builtins where
  open Declarative.Examples.StdLib.ChurchNat

  con2 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (^ integer)
  con2 = con {A = ^ integer} (pos 2) (refl≡β (^ (atomic aInteger)))

  builtin2plus2 : ∅ ⊢ con (^ integer)
  builtin2plus2 = builtin addInteger · con2 · con2

  builtininc2 : ∅ ⊢ con (^ integer)
  builtininc2 = inc · con2
```


### Scott Numerals

From <http://lucacardelli.name/Papers/Notes/scott2.pdf>

```
{-
    M = μ X . G X
    G X = ∀ R. R → (X → R) → R)
    μ X . G X = ∀ X . (G X → X) → X -- what is the status of this?
    N = G M
    in  : N → M
    out : M → N
    
    0    = Λ R . λ x : R . λ y : M → R . x
         : N
    succ = λ n : N . Λ R . λ x : R . λ y : M → R . y (in n)
         : N → N
    mycase = λ n : N . Λ R . λ a : R . λ f : N → N . n [R] a (f ∘ out)
         : N → ∀ R . R → (N → R) → R
-}

```

```
{-
module ScottE where
  G : ∀{Γ} → Γ ,⋆  * ⊢⋆ *
  G = Π (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)
  
  M : ∀{Γ} → Γ ⊢⋆ *
  M = μ G
  
  N : ∀{Γ} → Γ ⊢⋆ *
  N  =  G ⋆.[ M ]
  
  Zero : ∀{Γ} → Γ ⊢ N
  Zero = Λ (ƛ (ƛ (` (S (Z )))))
  
  Succ : ∀{Γ} → Γ ⊢ N ⇒ N
  Succ = ƛ (Λ (ƛ (ƛ (` Z · wrap G • (` (S (S (T Z)))) refl))))
  
  One : ∀{Γ} → Γ ⊢ N
  One = Succ · Zero
  
  Two : ∀{Γ} → Γ ⊢ N
  Two = Succ · One

  Three : ∅ ⊢ N
  Three = Succ · Two

  Four : ∅ ⊢ N
  Four = Succ · Three

  mycase : ∀{Γ} → Γ ⊢ N ⇒ (Π (` Z ⇒ (N ⇒ ` Z) ⇒ ` Z))
  mycase = ƛ (Λ (ƛ (ƛ ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (ƛ (` (S Z) · unwrap • refl (` Z)))))))

  -- Y : (a -> a) -> a
  -- Y f = (\x. f (x x)) (\x. f (x x))
  -- Y f = (\x : mu x. x -> a. f (x x)) (\x : mu x. x -> a. f (x x)) 

  Y-comb : ∀{Γ} → Γ ⊢ Π ((` Z ⇒ ` Z) ⇒ ` Z)
  Y-comb = Λ (ƛ ((ƛ (` (S Z) · (unwrap • refl (` Z) · (` Z)))) · wrap (` Z ⇒ ` (S Z)) • (ƛ (` (S Z) · (unwrap • refl (` Z) · (` Z)))) refl ))

  -- Z : ((a -> b) -> a -> b) -> a -> b
  -- Z f = (\r. f (\x. r r x)) (\r. f (\x. r r x))
  -- Z f = (\r : mu x. x -> a -> b. (\x : a. r r x)) (\r : mu x. x -> a -> b. (\x : a. r r x))

  Z-comb : ∀{Γ} →
    Γ ⊢ Π {- a -} (Π {- b -} (((` (S Z) ⇒ ` Z) ⇒ ` (S Z) ⇒ ` Z) ⇒ ` (S Z) ⇒ ` Z))
  Z-comb = Λ {- a -} (Λ {- b -} (ƛ {- f -} (ƛ {- r -} (` (S Z) · ƛ {- x -} (unwrap • refl (` (S Z)) · ` (S Z) · ` Z)) · wrap (` Z ⇒ ` (S (S Z)) ⇒ ` (S Z)) • (ƛ {- r -} (` (S Z) · ƛ {- x -} (unwrap • refl (` (S Z)) · ` (S Z) · ` Z))) refl)))

  TwoPlus : ∀{Γ} → Γ ⊢ (N ⇒ N) ⇒ N ⇒ N
  TwoPlus = ƛ (ƛ ((((mycase · (` Z)) ·⋆ N) · Two) · (ƛ (Succ · (` (S (S Z)) · (` Z))))))

  TwoPlusOne : ∅ ⊢ N
  -- TwoPlusTwo = Y-comb ·⋆ (N ⇒ N) · TwoPlus · Two
  TwoPlusOne = (Z-comb ·⋆ N) ·⋆ N · TwoPlus · One


  -- Roman's more efficient version
  Plus : ∀ {Γ} → Γ ⊢ N ⇒ N ⇒ N
  Plus = ƛ (ƛ ((Z-comb ·⋆ N) ·⋆ N · (ƛ (ƛ ((((mycase · ` Z) ·⋆ N) · ` (S (S (S Z)))) · (ƛ (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

  TwoPlusTwo : ∅ ⊢ N
  TwoPlusTwo = (Plus · Two) · Two
-}
```

```
{-
eval (gas 10000000) Scott.Four

(done
 (Λ
  (ƛ
   (ƛ
    ((` Z) ·
     wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
     (Λ
      (ƛ
       (ƛ
        ((` Z) ·
         wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
         (Λ
          (ƛ
           (ƛ
            ((` Z) ·
             wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
             (Λ
              (ƛ
               (ƛ
                ((` Z) ·
                 wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
                 (Λ (ƛ (ƛ (` (S Z)))))))))))))))))))))
 .Term.Reduction.Value.V-Λ_)

eval (gas 10000000) Scott.Two
(done
 (Λ
  (ƛ
   (ƛ
    ((` Z) ·
     wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
     (Λ
      (ƛ
       (ƛ
        ((` Z) ·
         wrap (Π (` Z) ⇒ ((` (S Z)) ⇒ (` Z)) ⇒ (` Z))
         (Λ (ƛ (ƛ (` (S Z)))))))))))))
 .Term.Reduction.Value.V-Λ_)
-}
```


```
module Scott1 where
  open import Declarative.Examples.StdLib.Nat
  
  One : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  One = Succ · Zero
  
  Two : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  Two = Succ · One

  Three : ∅ ⊢ N
  Three = Succ · Two

  Four : ∅ ⊢ N
  Four = Succ · Three

  mycase : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ (Π (` Z ⇒ (N ⇒ ` Z) ⇒ ` Z))
  mycase = ƛ (Λ (ƛ (ƛ (` (S (S (T Z))) ·⋆ ` Z · ` (S Z) · ƛ (` (S Z) · conv (β≡β _ _) (unwrap0 _ (` Z)))))))

  TwoPlus : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ (N ⇒ N) ⇒ N ⇒ N
  TwoPlus = ƛ (ƛ ((((mycase · (` Z)) ·⋆ N) · Two) · (ƛ (Succ · (` (S (S Z)) · (` Z))))))

  TwoPlusOne : ∅ ⊢ N
  TwoPlusOne = (Z-comb ·⋆ N) ·⋆ N · TwoPlus · One

  -- Roman's more efficient version
  Plus : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N ⇒ N
  Plus = ƛ (ƛ ((Z-comb ·⋆ N) ·⋆ N · (ƛ (ƛ ((((mycase · ` Z) ·⋆ N) · ` (S (S (S Z)))) · (ƛ (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

  TwoPlusTwo : ∅ ⊢ N
  TwoPlusTwo = (Plus · Two) · Two
```

### Church Numerals

```
module Church where
  open Declarative.Examples.StdLib.ChurchNat
  
  -- two plus two
  One : ∅ ⊢ N
  One = Succ · Zero

  Two : ∅ ⊢ N
  Two = Succ · One

  Three : ∅ ⊢ N
  Three = Succ · Two

  Four : ∅ ⊢ N
  Four = Succ · Three

  Plus : ∅ ⊢ N → ∅ ⊢ N → ∅ ⊢ N
  Plus x y = Iter ·⋆ N · x · Succ · y -- by induction on the second y

  TwoPlusTwo = Plus Two Two

  TwoPlusTwo' : ∅ ⊢ N
  TwoPlusTwo' = Two ·⋆ N · Two · Succ
```

```
{-
-- Church "4"
eval (gas 100000000) Four
(done
 (Λ
  (ƛ
   (ƛ
    (` Z) ·
    (((Λ
       (ƛ
        (ƛ
         (` Z) ·
         (((Λ
            (ƛ
             (ƛ
              (` Z) ·
              (((Λ
                 (ƛ
                  (ƛ
                   (` Z) · (((Λ (ƛ (ƛ (` (S Z))))) ·⋆ (` Z)) · (` (S Z)) · (` Z)))))
                ·⋆ (` Z))
               · (` (S Z))
               · (` Z)))))
           ·⋆ (` Z))
          · (` (S Z))
          · (` Z)))))
      ·⋆ (` Z))
     · (` (S Z))
     · (` Z)))))
 V-Λ_)

-- Church "2 + 2" using iterator
eval (gas 100000000) (Plus Two Two)

(done
 (Λ
  (ƛ
   (ƛ
    (` Z) ·
    (((Λ
       (ƛ
        (ƛ
         (` Z) ·
         (((Λ
            (ƛ
             (ƛ
              (` Z) ·
              (((Λ
                 (ƛ
                  (ƛ
                   (` Z) · (((Λ (ƛ (ƛ (` (S Z))))) ·⋆ (` Z)) · (` (S Z)) · (` Z)))))
                ·⋆ (` Z))
               · (` (S Z))
               · (` Z)))))
           ·⋆ (` Z))
          · (` (S Z))
          · (` Z)))))
      ·⋆ (` Z))
     · (` (S Z))
     · (` Z)))))
 V-Λ_)

-- Church "2 + 2" using the numerals directly
eval (gas 10000000) (Two ·⋆ N · Two · Succ)

(done
 (Λ
  (ƛ
   (ƛ
    ((` Z) ·
     ((((Λ
         (ƛ
          (ƛ
           ((` Z) ·
            ((((Λ
                (ƛ
                 (ƛ
                  ((` Z) ·
                   ((((Λ
                       (ƛ
                        (ƛ
                         ((` Z) ·
                          ((((Λ (ƛ (ƛ (` (S Z))))) ·⋆ (` Z)) · (` (S Z))) · (` Z))))))
                      ·⋆ (` Z))
                     · (` (S Z)))
                    · (` Z))))))
               ·⋆ (` Z))
              · (` (S Z)))
             · (` Z))))))
        ·⋆ (` Z))
       · (` (S Z)))
      · (` Z))))))
 V-Λ_)
-}
```
