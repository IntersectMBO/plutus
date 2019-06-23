\begin{code}
module Algorithmic.Examples where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
import Type.RenamingSubstitution as ⋆
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Algorithmic.Evaluation

open import Relation.Binary.PropositionalEquality renaming (subst to substEq)
\end{code}

## Examples

### Scott Numerals

From http://lucacardelli.name/Papers/Notes/scott2.pdf

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
case = λ n : N . Λ R . λ a : R . λ f : N → N . n [R] a (f ∘ out)
     : N → ∀ R . R → (N → R) → R


--

\begin{code}
-- bound variable names inserted below are not meaningful
module Scott where
  open import Type.BetaNBE
  open import Type.BetaNBE.Stability

  _·Nf_ : ∀{Γ}{K J}
    → Γ ⊢Nf⋆ K ⇒ J
    → Γ ⊢Nf⋆ K
    → Γ ⊢Nf⋆ J
  f ·Nf a = nf (embNf f · embNf a)

  μ0 : ∀{Γ} → Γ ⊢Nf⋆ (* ⇒ *) ⇒ *
  μ0 = ƛ "x" (ne (μ1 · ƛ "t" (ƛ "z" (ne (` Z · ne (` (S Z) · ne (` Z))))) · ne (` Z)))

  wrap0 : ∀{Φ Γ}
    → (A : Φ ⊢Nf⋆ * ⇒ *)
    → Γ ⊢ A ·Nf (μ0 ·Nf A)
    → Γ ⊢ μ0 ·Nf A
  wrap0 A X rewrite stability A = wrap1 _ A X

  unwrap0 : ∀{Φ Γ}
    → (A : Φ ⊢Nf⋆ * ⇒ *)
    → Γ ⊢ μ0 ·Nf A
    → Γ ⊢ A ·Nf (μ0 ·Nf A)
  unwrap0 A X rewrite stability A = unwrap1 X
  
  G : ∀{Γ} → Γ ,⋆  * ⊢Nf⋆ *
  G = Π "α" (ne (` Z) ⇒ (ne (` (S Z)) ⇒ ne (` Z)) ⇒ ne (` Z))
  
  M : ∀{Γ} → Γ ⊢Nf⋆ *
  M = μ0 ·Nf ƛ "x" G

  N : ∀{Γ} → Γ ⊢Nf⋆ *
  N  =  G [ M ]Nf

  Zero : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  Zero = Λ "α" (ƛ "x" (ƛ "y" (` (S (Z )))))


  Succ :  ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N
  Succ = ƛ "x" (Λ "α" (ƛ "y" (ƛ "z" (` Z · wrap0 (ƛ "x" G) (` (S (S (T Z))))))))

  One :  ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  One = Succ · Zero
  
  Two :  ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  Two = Succ · One

  Three : ∅ ⊢ N
  Three = Succ · Two

  Four : ∅ ⊢ N
  Four = Succ · Three

  case :  ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ (Π "α" (ne (` Z) ⇒ (N ⇒ ne (` Z)) ⇒ ne (` Z)))
  case = ƛ "x" (Λ "α" (ƛ "y" (ƛ "z" ((` (S (S (T Z)))) ·⋆ ne (` Z) · (` (S Z)) · (ƛ "a" (` (S Z) ·  unwrap0 (ƛ "x" G) (` Z) ))))))

{-
  Y-comb : ∀{Γ} → Γ ⊢ Π ((ne (` Z) ⇒ ne (` Z)) ⇒ ne (` Z))
  Y-comb = Λ (ƛ ((ƛ (` (S Z) · (unwrap • refl (` Z) · (` Z)))) · wrap (ne (` Z) ⇒ ne (` (S Z))) • (ƛ (` (S Z) · (unwrap • refl (` Z) · (` Z)))) refl ))
-}
  Z-comb :  ∀{Φ}{Γ : Ctx Φ} →
    Γ ⊢ Π "α" (Π "β" (((ne (` (S Z)) ⇒ ne (` Z)) ⇒ ne (` (S Z)) ⇒ ne (` Z)) ⇒ ne (` (S Z)) ⇒ ne (` Z)))
  Z-comb = Λ "α" (Λ "β" (ƛ "f" (ƛ "r" (` (S Z) · ƛ "x" (unwrap0  (ƛ "y" (ne (` Z) ⇒ ne (` (S (S Z))) ⇒ ne (` (S Z))))  (` (S Z)) · ` (S Z) · ` Z)) · wrap0 (ƛ "y" (ne (` Z) ⇒ ne (` (S (S Z))) ⇒ ne (` (S Z)))) (ƛ "r" (` (S Z) · ƛ "x" (unwrap0 (ƛ "y" (ne (` Z) ⇒ ne (` (S (S Z))) ⇒ ne (` (S Z)))) (` (S Z)) · ` (S Z) · ` Z))))))

  OnePlus :  ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ (N ⇒ N) ⇒ N ⇒ N
  OnePlus = ƛ "x" (ƛ "y" ((((case · (` Z)) ·⋆ N) · One) · (ƛ "z" (Succ · (` (S (S Z)) · (` Z))))))

  OnePlusOne : ∅ ⊢ N
  OnePlusOne = (Z-comb ·⋆ N) ·⋆ N · OnePlus · One

 -- Roman's more efficient version
  Plus : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N ⇒ N ⇒ N
  Plus = ƛ "x" (ƛ "y" ((Z-comb ·⋆ N) ·⋆ N · (ƛ "x" (ƛ "y" ((((case · ` Z) ·⋆ N) · ` (S (S (S Z)))) · (ƛ "x" (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

  TwoPlusTwo : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ N
  TwoPlusTwo = (Plus · Two) · Two
\end{code}

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

### Church Numerals

\begin{code}
module Church where

  N :  ∀{Φ} → Φ ⊢Nf⋆ *
  N = Π "α" ((ne (` Z)) ⇒ (ne (` Z) ⇒ ne (` Z)) ⇒ (ne (` Z)))

  Zero : ∅ ⊢ N
  Zero = Λ "α" (ƛ "x" (ƛ "y" (` (S Z))))

  Succ : ∅ ⊢ N ⇒ N
  Succ = ƛ "x" (Λ "α" (ƛ "y" (ƛ "z" (` Z · ((` (S (S (T Z)))) ·⋆ (ne (` Z)) · (` (S Z)) · (` Z))))))
  
  Iter : ∅ ⊢ Π "α" (ne (` Z) ⇒ (ne (` Z) ⇒ ne (` Z)) ⇒ N ⇒ ne (` Z))
  Iter = Λ "α" (ƛ "x" (ƛ "y" (ƛ "z" ((` Z) ·⋆ ne (` Z) · (` (S (S Z))) · (` (S Z))))))

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

open Church public
\end{code}

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
