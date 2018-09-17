\begin{code}
module Type.NBE where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.Normal
open import Type.RenamingSubstitution

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
open import Function
open import Data.Product
\end{code}

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J
\end{code}

\begin{code}
Val : Ctx⋆ → Kind → Set
Val Γ * = Γ ⊢Nf⋆ *
Val Γ (K ⇒ J) = ∀{Δ} → Ren Γ Δ → Val Δ K → Val Δ J

renval : ∀{Γ Δ} σ → Ren Γ Δ → Val Γ σ → Val Δ σ
renval * ρ v = renameNf ρ v
renval (K ⇒ J) ρ f = λ ρ' v → f (ρ' ∘ ρ) v

mutual
  reify : ∀{Γ} K → Val Γ K → Γ ⊢Nf⋆ K
  reify * (Π B) = Π B
  reify * (A ⇒ B) = A ⇒ B
  reify * (μ B) = μ B
  reify * (ne A) = ne A
  reify (K ⇒ J) f = ƛ (reify J (f S (reflect K (` Z)))) 
  
  reflect : ∀{Γ} K → Γ ⊢NeN⋆ K → Val Γ K
  reflect * n = ne n
  reflect (K ⇒ J) f = (λ ρ x → reflect J (renameNeN ρ f · (reify K x)))

-- A Partial equivalence relation on values: 'equality on values'
PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
PER *       v v' = reify * v ≡ reify * v'
PER (K ⇒ J) f f' = ∀{Δ}
 → (ρ : Ren _ Δ)
 → {v v' : Val Δ K}
 → PER K v v'
 → PER J (f ρ v) (f' ρ v')  


symPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v' v
symPER *       p = sym p
symPER (K ⇒ J) p = λ ρ q → symPER J (p ρ (symPER K q))

transPER : ∀{Γ} K {v v' v'' : Val Γ K} → PER K v v' → PER K v' v'' → PER K v v''
transPER * p q = trans p q
transPER (K ⇒ J) p q = λ ρ r
  → transPER J (p ρ r) (q ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v v
reflPER K p = transPER K p (symPER K p)

mutual
  reifyPER : ∀{Γ} K {v v' : Val Γ K}
    → PER K v v'
    → reify K v ≡ reify K v'
  reifyPER *       p = p
  reifyPER (K ⇒ J) p = cong ƛ (reifyPER J (p S (reflectPER K (refl {x = ` Z})))) 
  
  reflectPER  : ∀{Γ} K {n n' : Γ ⊢NeN⋆ K}
    → n ≡ n'
    → PER K (reflect K n) (reflect K n')
  reflectPER *       p = cong ne p
  reflectPER (K ⇒ J) p =
   λ ρ q → reflectPER J (cong₂ _·_ (cong (renameNeN ρ) p) (reifyPER K q))
\end{code}
  
\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J

_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
eval (` x)    ρ = ρ x
eval (Π B)    ρ = Π (eval B ((renval _ S ∘ ρ) ,,⋆ reflect _ (` Z)))
eval (A ⇒ B) ρ = eval A ρ ⇒ eval B ρ
eval (ƛ B)    ρ = λ ρ' v → eval B ((renval _ ρ' ∘ ρ) ,,⋆ v)
eval (A · B) ρ = eval A ρ id (eval B ρ)
eval (μ B)    ρ = μ (eval B ((renval _ S ∘ ρ) ,,⋆ reflect _ (` Z)))
\end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z = reflect K (` Z)
idEnv (Γ ,⋆ K) (S x) = renval _ S (idEnv Γ x)
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = reify _ (eval t (idEnv _))
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = nf (embNf A [ embNf B ])
\end{code}

