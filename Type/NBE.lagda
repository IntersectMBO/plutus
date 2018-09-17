\begin{code}
module Type.NBE where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.Normal

open import Function
\end{code}

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J

Val : Ctx⋆ → Kind → Set
Val Γ * = Γ ⊢Nf⋆ *
Val Γ (K ⇒ J) = ∀{Δ} → Ren Γ Δ → Val Δ K → Val Δ J
\end{code}

\begin{code}
reflect : ∀{Γ} K → Γ ⊢NeN⋆ K → Val Γ K

reify : ∀{Γ} K → Val Γ K → Γ ⊢Nf⋆ K
reify * (Π B) = Π B
reify * (A ⇒ B) = A ⇒ B
reify * (μ B) = μ B
reify * (ne A) = ne A
reify (K ⇒ J) f = ƛ (reify J (f S (reflect K (` Z)))) 

reflect * n = ne n
reflect (K ⇒ J) f = λ ρ x → reflect J (renameNeN ρ f · (reify K x))
\end{code}

\begin{code}
val : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
renval : ∀{Γ Δ} σ → Ren Γ Δ → Val Γ σ → Val Δ σ

val (` x)    ρ = ρ x
val (Π B)    ρ = Π (val B (λ { Z → reflect _ (` Z) ; (S x) → renval _ S (ρ x)}))
val (A ⇒ B) ρ = val A ρ ⇒ val B ρ
val (ƛ B)    ρ = λ ρ' x → val B λ { Z → x ; (S x) → renval _ ρ' (ρ x)}
val (A · B) ρ with val A ρ
... | p = p id (val B ρ)
val (μ B)    ρ = μ (val B (λ { Z → reflect _ (` Z) ; (S x) → renval _ S (ρ x)}))

renval * ρ v = renameNf ρ v
renval (K ⇒ J) ρ f = λ ρ' v → f (ρ' ∘ ρ) v
\end{code}
