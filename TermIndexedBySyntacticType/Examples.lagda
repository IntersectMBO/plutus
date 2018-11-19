\begin{code}
module TermIndexedBySyntacticType.Examples where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Type.Equality
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Term.RenamingSubstitution
open import TermIndexedBySyntacticType.Evaluation
open import Builtin.Constant.Type
open import Builtin.Constant.Term
open import Builtin.Signature

open import Relation.Binary.PropositionalEquality renaming (subst to substEq)
open import Function
open import Agda.Builtin.Int
open import Data.Integer
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Data.Unit
\end{code}

## Examples

\begin{code}
module Builtins where
  con1 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
  con1 = con (integer 8 (pos 1) (-≤+ ,, (+≤+ (s≤s (s≤s z≤n)))))

  con2 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
  con2 = con (integer 8 (pos 2) (-≤+ ,, +≤+ (s≤s (s≤s (s≤s z≤n)))))

  builtin2plus2 : ∅ ⊢ con integer (size⋆ 8)
  builtin2plus2 = builtin
    addInteger
    (λ { Z → size⋆ 8 ; (S x) → ` x})
    (con2 ,, con2 ,, tt)

  inc8 : ∅ ⊢ con integer (size⋆ 8) ⇒ con integer (size⋆ 8)
  inc8 = ƛ (builtin
    addInteger
    (λ { Z → size⋆ 8 ; (S x) → ` x})
    (con1 ,, ` Z ,, tt))

  builtininc2 : ∅ ⊢ con integer (size⋆ 8)
  builtininc2 = inc8 · con2

  inc : ∅ ⊢ Π (con integer (` Z) ⇒ con integer (` Z))
  inc = Λ (ƛ (builtin addInteger ` ((builtin resizeInteger (λ { Z → ` Z ; (S Z) → size⋆ 8 ; (S (S ()))}) (builtin sizeOfInteger ` (` Z ,, tt) ,, (con1 ,, tt))) ,, (` Z) ,, tt)))

  builtininc2' : ∅ ⊢ con integer (size⋆ 8)
  builtininc2' = (inc ·⋆ size⋆ 8) · con2
\end{code}


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

  case : ∀{Γ} → Γ ⊢ N ⇒ (Π (` Z ⇒ (N ⇒ ` Z) ⇒ ` Z))
  case = ƛ (Λ (ƛ (ƛ ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (ƛ (` (S Z) · unwrap • refl (` Z)))))))

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
  TwoPlus = ƛ (ƛ ((((case · (` Z)) ·⋆ N) · Two) · (ƛ (Succ · (` (S (S Z)) · (` Z))))))

  TwoPlusOne : ∅ ⊢ N
  -- TwoPlusTwo = Y-comb ·⋆ (N ⇒ N) · TwoPlus · Two
  TwoPlusOne = (Z-comb ·⋆ N) ·⋆ N · TwoPlus · One


  -- Roman's more efficient version
  Plus : ∀ {Γ} → Γ ⊢ N ⇒ N ⇒ N
  Plus = ƛ (ƛ ((Z-comb ·⋆ N) ·⋆ N · (ƛ (ƛ ((((case · ` Z) ·⋆ N) · ` (S (S (S Z)))) · (ƛ (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

  TwoPlusTwo : ∅ ⊢ N
  TwoPlusTwo = (Plus · Two) · Two
-}
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



\begin{code}
module Scott1 where

  μ0 : ∀{Γ} → Γ ⊢⋆ (* ⇒ *) ⇒ *
  μ0 = ƛ (μ1 · ƛ (ƛ (` (S (S Z)) · (` (S Z) · ` Z))) · Π (` Z))

{-
  wrap0 : ∀{Γ}(pat : ∥ Γ ∥ ⊢⋆ * ⇒ *) → Γ ⊢ μ0 · pat
  wrap0 M = {!!}
-}

  wrap0 : ∀{Γ}(pat : ∥ Γ ∥ ⊢⋆ * ⇒ *) → Γ ⊢ pat ·  (μ0 · pat) → Γ ⊢ μ0 · pat
  wrap0 {Γ} pat X = conv
    (sym≡β (β≡β _ _))
    (wrap1
      (ƛ (ƛ (⋆.weaken (⋆.weaken pat) · (` (S Z) · ` Z))))
      (Π (` Z))
      (conv
        (·≡β (sym≡β (β≡β _ _)) (refl≡β _))
        (conv
          (sym≡β (β≡β _ _))
          (substEq
            (Γ ⊢_)
            (cong₂
              _·_
              (trans
                (trans
                  (trans (sym (⋆.subst-id pat)) (⋆.subst-rename pat))
                  (⋆.subst-rename (⋆.weaken pat)))
                (⋆.subst-comp (⋆.weaken (⋆.weaken pat))))
              (cong
                (λ x → μ1 · x · Π (` Z))
                (cong
                  ƛ
                  (cong
                    ƛ
                    (cong
                      (_· (` (S Z) · ` Z))
                      (trans
                        (trans
                          (trans
                            (trans
                              (trans
                                (sym (⋆.rename-comp pat))
                                (sym
                                  (⋆.subst-id (⋆.rename (λ x → S (S x)) pat))))
                              (sym
                                (⋆.subst-rename {g = λ x → S (S x)}{`} pat)))
                            (⋆.subst-rename pat))
                          (⋆.subst-rename (⋆.weaken pat)))
                        (⋆.subst-rename (⋆.weaken (⋆.weaken pat)))))))))
            (conv (·≡β (refl≡β _) (β≡β _ _)) X)))))

  G : ∀{Γ} → Γ ,⋆  * ⊢⋆ *
  G = Π (` Z ⇒ (` (S Z) ⇒ ` Z) ⇒ ` Z)
  
  M : ∀{Γ} → Γ ⊢⋆ *
  M {Γ} = μ1 {K = *} · ƛ (ƛ (ƛ G · (` (S Z) · ` Z))) · unit

  N : ∀{Γ} → Γ ⊢⋆ *
  N  =  G ⋆.[ M ]

  Zero : ∀{Γ} → Γ ⊢ N
  Zero = Λ (ƛ (ƛ (` (S (Z )))))
{-  
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

  case : ∀{Γ} → Γ ⊢ N ⇒ (Π (` Z ⇒ (N ⇒ ` Z) ⇒ ` Z))
  case = ƛ (Λ (ƛ (ƛ ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (ƛ (` (S Z) · unwrap • refl (` Z)))))))

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
  TwoPlus = ƛ (ƛ ((((case · (` Z)) ·⋆ N) · Two) · (ƛ (Succ · (` (S (S Z)) · (` Z))))))

  TwoPlusOne : ∅ ⊢ N
  -- TwoPlusTwo = Y-comb ·⋆ (N ⇒ N) · TwoPlus · Two
  TwoPlusOne = (Z-comb ·⋆ N) ·⋆ N · TwoPlus · One


  -- Roman's more efficient version
  Plus : ∀ {Γ} → Γ ⊢ N ⇒ N ⇒ N
  Plus = ƛ (ƛ ((Z-comb ·⋆ N) ·⋆ N · (ƛ (ƛ ((((case · ` Z) ·⋆ N) · ` (S (S (S Z)))) · (ƛ (Succ · (` (S (S Z)) · ` Z)))))) · ` (S Z)))

  TwoPlusTwo : ∅ ⊢ N
  TwoPlusTwo = (Plus · Two) · Two
-}
\end{code}


### Church Numerals

\begin{code}
module Church where
  N : ∀{Γ} → Γ ⊢⋆ *
  N = Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)

  Zero : ∅ ⊢ N
  Zero = Λ (ƛ (ƛ (` (S Z))))

  Succ : ∅ ⊢ N ⇒ N
  Succ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (` Z))))))
  
  Iter : ∅ ⊢ Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ N ⇒ (` Z))
  Iter = Λ (ƛ (ƛ (ƛ ((` Z) ·⋆ (` Z) · (` (S (S Z))) · (` (S Z))))))

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

--open Church public
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
