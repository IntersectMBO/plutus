\begin{code}
module Type.BetaNBE where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.RenamingSubstitution
open import Type.Equality

open import Function
open import Data.Sum
open import Data.Empty

open import Relation.Binary.PropositionalEquality hiding ([_])
\end{code}

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J
\end{code}

\begin{code}
Val : Ctx⋆ -> Kind -> Set
Val Γ  *      = Γ ⊢Nf⋆ *
Val Γ (σ ⇒ τ) = Γ ⊢NeN⋆ (σ ⇒ τ) ⊎ ∀ {Δ} -> Ren Γ Δ -> Val Δ σ -> Val Δ τ

neV : ∀{Γ σ} → Γ ⊢NeN⋆ σ → Val Γ σ
neV {σ = *}     n = ne n
neV {σ = σ ⇒ τ} n = inj₁ n

fresh : ∀ {Γ σ} -> Val (Γ ,⋆ σ) σ
fresh = neV (` Z)

renval : ∀ {σ Γ Δ} -> Ren Γ Δ -> Val Γ σ -> Val Δ σ
renval {*}     ψ n         = renameNf ψ n
renval {σ ⇒ τ} ψ (inj₁ n)  = inj₁ (renameNeN ψ n)
renval {σ ⇒ τ} ψ (inj₂ f)  = inj₂ (λ ρ' →  f (ρ' ∘ ψ))

readback : ∀ {σ Γ} -> Val Γ σ -> Γ ⊢Nf⋆ σ
readback {*}     n         = n
readback {σ ⇒ τ} (inj₁ n)  = ne n
readback {σ ⇒ τ} (inj₂ f)  = ƛ (readback (f S fresh))
\end{code}

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J

_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
_·V_ : ∀{Γ K J} → Val Γ (K ⇒ J) → Val Γ K → Val Γ J
inj₁ n ·V v = neV (n · readback v)
inj₂ f ·V v = f id v
\end{code}

\begin{code}
eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
eval (` x)   ρ = ρ x
eval (Π B)   ρ = Π (readback (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
eval (A ⇒ B) ρ = readback (eval A ρ) ⇒ readback (eval B ρ)
eval (ƛ B)   ρ = inj₂ λ ρ' v → eval B ((renval ρ' ∘ ρ) ,,⋆ v)
eval (A · B) ρ = eval A ρ ·V eval B ρ
eval (μ B)   ρ = μ (readback (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
\end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z     = fresh
idEnv (Γ ,⋆ K) (S x) = renval S (idEnv Γ x)
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = readback (eval t (idEnv _))
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = nf (embNf A [ embNf B ])
\end{code}

## Proofs

\begin{code}
mutual
  -- A Partial equivalence relation on values: 'equality on values'
  PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
  PER *       n n' = n ≡ n' -- the same as readback n ≡ readback n'
  PER (K ⇒ J) (inj₁ n) (inj₁ n') = readback (inj₁ n) ≡ readback (inj₁ n')
  PER (K ⇒ J) (inj₂ f) (inj₁ n') = ⊥ -- could only be eta equal I suspect
  PER (K ⇒ J) (inj₁ n) (inj₂ f)  = ⊥ -- could only be eta equal I suspect
  PER (K ⇒ J) (inj₂ f) (inj₂ f') = ∀ {Δ}
   → (ρ : Ren _ Δ)
   → {v v' : Val Δ K}
   → PER K v v'
   → PER J (renval ρ (inj₂ f) ·V v) (renval ρ (inj₂ f') ·V v')

symPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v' v
symPER *       p = sym p
symPER (K ⇒ J) {inj₁ x} {inj₁ x₁} p = sym p
symPER (K ⇒ J) {inj₁ x} {inj₂ y} ()
symPER (K ⇒ J) {inj₂ y} {inj₁ x} ()
symPER (K ⇒ J) {inj₂ y} {inj₂ y₁} p = λ ρ q → symPER J (p ρ (symPER K q))

transPER : ∀{Γ} K {v v' v'' : Val Γ K} → PER K v v' → PER K v' v'' → PER K v v''
transPER * p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₁ n''} p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₂ f''} p ()
transPER (K ⇒ J) {inj₁ n} {inj₂ f'} () q
transPER (K ⇒ J) {inj₂ f} {inj₁ n'} () q
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₁ n} p ()
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₂ f''} p q = 
 λ ρ r → transPER J (p ρ r) (q ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v v
reflPER K p = transPER K p (symPER K p)
\end{code}

\begin{code}
reflect : ∀{Γ} K → {n n' : Γ ⊢NeN⋆ K}
  → n ≡ n' → PER K (neV n) (neV n')
reflect * p = cong ne p
reflect (K ⇒ J) p = cong ne p


reify : ∀{Γ} K → {v v' : Val Γ K}
  → PER K v v' → readback v ≡ readback v'
reify *       p = p
reify (K ⇒ J) {inj₁ n} {inj₁ n'} p = p
reify (K ⇒ J) {inj₁ n} {inj₂ f'} ()
reify (K ⇒ J) {inj₂ f} {inj₁ n'} ()
reify (K ⇒ J) {inj₂ f} {inj₂ f'} p =
  cong ƛ (reify J (p S (reflect K (refl {x = ` Z}))))  
\end{code}

\begin{code}
PEREnv : ∀ {Γ Δ} → (η η' : Env Γ Δ) →  Set
PEREnv {Γ}{Δ} η η' = ∀{K} (x : Γ ∋⋆ K) → PER K (η x) (η' x) 
\end{code}

\begin{code}
PERApp : ∀{Γ K J}
  → {f f' : Val Γ (K ⇒ J)}
  → PER (K ⇒ J) f f'
  → {v v' : Val Γ K}
  → PER K v v'
  → PER J (f ·V v) (f' ·V v')
PERApp {f = inj₁ n} {inj₁ .n} refl q = reflect _ (cong (n ·_) (reify _ q))
PERApp {f = inj₁ n} {inj₂ f'} () q
PERApp {f = inj₂ f} {inj₁ n} () q
PERApp {f = inj₂ f} {inj₂ f'} p q = p id q
\end{code}

\begin{code}
PER,,⋆ : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → {v v' : Val Δ K}
  → PER K v v'
  → PEREnv (η ,,⋆ v) (η' ,,⋆ v')
PER,,⋆ p q Z = q
PER,,⋆ p q (S x) = p x
\end{code}

\begin{code}
renPER : ∀{Γ Δ K}{v v' : Val Γ K}
  → (ρ : Ren Γ Δ)
  → PER K v v'
  → PER K (renval ρ v) (renval ρ v')
renPER {K = *} {v} {v'} ρ p = cong (renameNf ρ) p
renPER {K = K ⇒ K₁} {inj₁ n} {inj₁ .n} ρ refl = refl
renPER {K = K ⇒ K₁} {inj₁ n} {inj₂ f'} ρ ()
renPER {K = K ⇒ K₁} {inj₂ f} {inj₁ n'} ρ ()
renPER {K = K ⇒ K₁} {inj₂ f} {inj₂ f'} ρ p = λ ρ' q → p (ρ' ∘ ρ) q
\end{code}

-- completeness
\begin{code}
idext : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → (t : Γ ⊢⋆ K)
  → PER K (eval t η) (eval t η')
idext p (` x)   = p x
idext p (Π B)   = cong Π (idext (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) B)
idext p (A ⇒ B) = cong₂ _⇒_ (idext p A) (idext p B)
idext p (ƛ B)   = λ ρ q → idext (PER,,⋆ (renPER ρ ∘ p) q) B
idext p (A · B) = PERApp (idext p A) (idext p B)
idext p (μ  B)   = cong μ (idext (PER,,⋆ (renPER S ∘ p) refl) B)
\end{code}

\begin{code}
fund : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → {t t' : Γ ⊢⋆ K}
  → t ≡β t' → PER K (eval t η) (eval t' η')
fund η (refl≡β A) = idext η A
fund η (sym≡β p) = symPER _ (fund (symPER _ ∘ η) p)
fund η (trans≡β p q) = transPER _ (fund (reflPER _ ∘ η) p) (fund η q)
fund η `≡β = η _
fund η (⇒≡β p q) = cong₂ _⇒_ (fund η p) (fund η q)
fund η (Π≡β p) = cong Π (fund (PER,,⋆ (renPER S ∘ η) (reflect _ refl)) p)
fund η (ƛ≡β p) = λ ρ q → fund (PER,,⋆ (renPER ρ ∘ η) q) p
fund η (·≡β p q) = PERApp (fund η p) (fund η q)
fund η (μ≡β p) = cong μ (fund (PER,,⋆ (renPER S ∘ η) (reflect * refl)) p)
fund η β≡β = {!!}
\end{code}

\begin{code}
{-
rename-eval : ∀{Γ Δ Θ K}
  (t : Δ ⊢⋆ K)
  (η : ∀{J} → Δ ∋⋆ J → Val Γ J)
  (ρ : Ren Γ Θ) →
  PER K (renval ρ (eval t η)) (eval t (renval ρ ∘ η))
rename-eval (` x) η ρ = {!reflPER!}
rename-eval (Π B) η ρ = {!!}
rename-eval (A ⇒ B) η ρ = {!eval!}
rename-eval (ƛ B) η ρ = {!!}
rename-eval (A · B) η ρ = {!!}
rename-eval (μ B) η ρ = {!!}
-}
\end{code}

\begin{code}
{-
rename[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          ------
        → renameNf ρ (t [ u ]Nf) ≡ renameNf (ext ρ) t [ renameNf ρ u ]Nf
rename[]Nf ρ (Π B)   u = cong Π {!!}
rename[]Nf ρ (A ⇒ B) u = {!!}
rename[]Nf ρ (ƛ B)   u = {!!}
rename[]Nf ρ (μ B)   u = {!!}
rename[]Nf ρ (ne xn) u = {!!}
-}
\end{code}
