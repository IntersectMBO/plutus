\begin{code}
module Declarative.Examples.StdLib.Function where
\end{code}

\begin{code}
open import Type
open import Type.Equality
open import Declarative
\end{code}

These examples are pretty old and not used, I am only ensuring that they
continue to typecheck

\begin{code}
--/\ (A B :: *) -> \(x : A) (y : B) -> x
const : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π (Π (` (S Z) ⇒ ` Z ⇒ ` (S Z)))
const = Λ (Λ (ƛ (ƛ (` (S Z)))))

μ0 : ∀{Γ} → Γ ⊢⋆ (* ⇒ *) ⇒ *
μ0 = ƛ (μ (ƛ (ƛ (` Z · (` (S Z) · ` Z)))) (` Z))

wrap0 : ∀{Φ Γ}(pat : Φ ⊢⋆ * ⇒ *) → Γ ⊢ pat · (μ0 · pat) → Γ ⊢ μ0 · pat
wrap0 {Γ} pat X = conv
  (sym≡β (β≡β _ _))
  (wrap
    (ƛ (ƛ (` Z · (` (S Z) · ` Z))))
    pat
    (conv
      (trans≡β (sym≡β (β≡β _ _)) (·≡β (sym≡β (β≡β _ _)) (refl≡β _)))
      X))

unwrap0 : ∀{Φ Γ}(pat : Φ ⊢⋆ * ⇒ *) → Γ ⊢ μ0 · pat  → Γ ⊢ pat ·  (μ0 · pat)
unwrap0 {Γ} pat X = conv
  (trans≡β
    (·≡β (β≡β _ _) (refl≡β _))
    (β≡β _ _))
  (unwrap (conv (β≡β _ _) X))

{-
  -- Y : (a -> a) -> a
  -- Y f = (\x. f (x x)) (\x. f (x x))
  -- Y f = (\x : mu x. x -> a. f (x x)) (\x : mu x. x -> a. f (x x)) 

  -- Z : ((a -> b) -> a -> b) -> a -> b
  -- Z f = (\r. f (\x. r r x)) (\r. f (\x. r r x))
  -- Z f = (\r : mu x. x -> a -> b. f (\x : a. r r x)) (\r : mu x. x -> a -> b. f (\x : a. r r x))
-}

Z-comb : ∀{Φ}{Γ : Ctx Φ} →
  Γ ⊢ Π (Π (((` (S Z) ⇒ ` Z) ⇒ ` (S Z) ⇒ ` Z) ⇒ ` (S Z) ⇒ ` Z))
Z-comb = Λ (Λ (ƛ (ƛ (` (S Z) · ƛ (conv (β≡β _ _) (unwrap0 (ƛ (` Z ⇒ ` (S (S Z)) ⇒ ` (S Z))) (` (S Z))) · ` (S Z) · ` Z)) · wrap0 _ (conv (sym≡β (β≡β _ _)) (ƛ (` (S Z) · ƛ (conv (β≡β _ _) (unwrap0 (ƛ (` Z ⇒ ` (S (S Z)) ⇒ ` (S Z))) (` (S Z))) · ` (S Z) · ` Z)))))))

\end{code}
