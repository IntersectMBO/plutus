\begin{code}
module Type.BetaNBE.Soundness where
\end{code}

\begin{code}
open import Type
open import Type.Equality
open import Type.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNBE

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq)
  hiding ([_])
open import Function
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Data.String
\end{code}

The Soundness Relation (SR) is a Kripke logical relation between types
and their values. It is defined by induction on kinds. it says that a type
is related to a value if when we reach ground kind (# or *) then the
type is beta-eta-equal to the result of reifying the value.

\begin{code}
SR : ∀{Φ} K → Φ ⊢⋆ K → Val Φ K → Set
SR *       A v        = A ≡β embNf v
SR (K ⇒ J) A (inj₁ n) = A ≡β embNe n
SR (K ⇒ J) A (inj₂ f) = Σ (_ ,⋆ K ⊢⋆ J) λ B →
  (A ≡β ƛ B) -- this bit of indirection is needed as we have only β not βη
  ×
  ∀{Ψ}
    → (ρ : Ren _ Ψ)
    → {u : Ψ ⊢⋆ K}
    → {v : Val Ψ K}
    → SR K u v
      -----------------------------------------------------
    → SR J (ren ρ (ƛ B) · u) (renVal ρ (inj₂ f) ·V v)
\end{code}

\begin{code}
reflectSR : ∀{Φ K}{A : Φ ⊢⋆ K}{n : Φ ⊢Ne⋆ K}
  → A ≡β embNe n
    ------------------
  → SR K A (reflect n)
reflectSR {K = *}     p = p
reflectSR {K = K ⇒ J} p = p

reifySR : ∀{Φ K}{A : Φ ⊢⋆ K}{v : Val Φ K}
  → SR K A v
    --------------------
  → A ≡β embNf (reify v)
reifySR {K = *}                  p            = p
reifySR {K = K ⇒ J} {v = inj₁ n} p            = p
reifySR {K = K ⇒ J} {v = inj₂ f} (A' , p , q) = trans≡β
  p
  (trans≡β (≡2β (cong ƛ (trans (trans (sym (subst-id A')) (subst-cong (λ { Z → refl ; (S α) → refl}) A')) (subst-ren A'))))
           (ƛ≡β (trans≡β (sym≡β (β≡β _ _))
                         (reifySR (q S (reflectSR (refl≡β (` Z))))))))
\end{code}

Lifting SR from ⊢⋆/Val to Sub/Env

\begin{code}
SREnv : ∀{Φ Ψ} → Sub Φ Ψ → Env Φ Ψ → Set
SREnv {Φ} σ η = ∀{K}(α : Φ ∋⋆ K) → SR K (σ α) (η α)
\end{code}

Cons for SREnv

\begin{code}
SR,,⋆ : ∀{Φ Ψ}{σ : Sub Φ Ψ}{η : Env Φ Ψ}
  → SREnv σ η
  → ∀{K}{A : Ψ ⊢⋆ K}{v : Val Ψ K}
  → SR K A v
  → SREnv (subst-cons σ A) (η ,,⋆ v)
SR,,⋆ p q Z     = q
SR,,⋆ p q (S α) = p α
\end{code}

SR is closed under ≡β

\begin{code}
substSR : ∀{Φ K}{A A' : Φ ⊢⋆ K}
  → A' ≡β A
  → {v : Val Φ K}
  → SR K A v
    ---------------------------
  → SR K A' v
substSR {K = *}     p          q            = trans≡β p q
substSR {K = K ⇒ J} p {inj₁ n} q            = trans≡β p q
substSR {K = K ⇒ J} p {inj₂ f} (A' , q , r) = _ , trans≡β p q , r
\end{code}

renaming for SR

\begin{code}
renSR : ∀{Φ Ψ}(ρ : Ren Φ Ψ){K}{A : Φ ⊢⋆ K}{v : Val Φ K}
  → SR K A v
    ---------------------------------
  → SR K (ren ρ A) (renVal ρ v)
renSR ρ {*}{A}{n} p = trans≡β (ren≡β ρ p) (sym≡β (≡2β (ren-embNf ρ n)))
renSR ρ {K ⇒ J} {A} {inj₁ n} p =
  trans≡β (ren≡β ρ p) (sym≡β (≡2β (ren-embNe ρ n)))
renSR ρ {K ⇒ J} {A} {inj₂ f} (A' , p , q) =
  ren (ext ρ) A'
  ,
  ren≡β ρ p
  ,
  λ ρ' {u}{v} r → substSR
    (≡2β (cong₂ _·_ (cong ƛ (trans (sym (ren-comp A'))
                           (ren-cong (sym ∘ ext-comp) A'))) refl))
    (q (ρ' ∘ ρ) r)
\end{code}

Extending via exts is the same the same as weakening and cons on ` Z

\begin{code}
exts-subst-cons : ∀{Φ Ψ K J}
  → (σ : Sub Φ Ψ)
  → (α : Φ ,⋆ J ∋⋆ K)
  → exts σ α ≡ subst-cons (weaken ∘ σ) (` Z) α
exts-subst-cons σ Z     = refl
exts-subst-cons σ (S _) = refl
\end{code}

SREnv is closed under (pointwise) equality of environments

\begin{code}
substSREnv : ∀{Φ Ψ}{σ σ' : Sub Φ Ψ}
  → (∀{K}(α : Φ ∋⋆ K) → σ α ≡ σ' α)
  → {η : Env Φ Ψ}
  → SREnv σ η
    -------------------------------
  → SREnv σ' η
substSREnv p q α rewrite sym (p α) = q α
\end{code}

SREnv is closed under exts/extending the env
(note: would this be cleaner if we used exte?)

\begin{code}
SRweak : ∀{Φ Ψ}{σ : Sub Φ Ψ}{η : Env Φ Ψ}
  → SREnv σ η
  → ∀ {K}
    -------------------------------------------------------
  → SREnv (exts σ) ((renVal S ∘ η) ,,⋆ fresh {σ = K})
SRweak p = substSREnv (sym ∘ exts-subst-cons _)
                      (SR,,⋆ (renSR S ∘ p) (reflectSR (refl≡β (` Z)))) 
\end{code}

SR is closed under ·V

\begin{code}
SRApp : ∀{Φ K J}
  → {A : Φ ⊢⋆ (K ⇒ J)}
  → {f : Val Φ (K ⇒ J)}
  → SR (K ⇒ J) A f
  → {u : Φ ⊢⋆ K}
  → {v : Val Φ K}
  → SR K u v
    ---------------------
  → SR J (A · u) (f ·V v)
SRApp {f = inj₁ n} p            q = reflectSR (·≡β (reflectSR p) (reifySR q))
SRApp {f = inj₂ f} (A' , p , q) r = substSR
  (·≡β
    (trans≡β
      p
      (≡2β (cong ƛ (trans (sym (ren-id A')) (ren-cong (sym ∘ ext-id) A')))))
    (refl≡β _))
  (q id r)
\end{code}

Fundamental Theorem of Logical Relations for SR

\begin{code}
evalSR : ∀{Φ Ψ K}(A : Φ ⊢⋆ K){σ : Sub Φ Ψ}{η : Env Φ Ψ}
  → SREnv σ η
  → SR K (subst σ A) (eval A η)
evalSR (` α)                   p = p α
evalSR (Π B)                   p = Π≡β (evalSR B (SRweak p))
evalSR (A ⇒ B)                 p = ⇒≡β (evalSR A p) (evalSR B p)
evalSR (ƛ B)   {σ}{η}          p =
  subst (exts σ) B
  ,
  refl≡β _
  ,
  λ ρ {u}{v} q → substSR
    (trans≡β (β≡β _ _) (≡2β (trans
      (sym (subst-ren (subst (exts σ) B)))
      (trans
        (sym (subst-comp B))
        (subst-cong (λ { Z → refl
                       ; (S α) → trans
                            (sym (subst-ren (σ α)))
                            (trans (subst-ren (σ α))
                                    (subst-id (ren ρ (σ α))))})
                    B)))))
    (evalSR B (SR,,⋆ (renSR ρ ∘ p) q))
evalSR (A · B)     p = SRApp (evalSR A p) (evalSR B p)
evalSR (μ A B)     p = μ≡β (reifySR (evalSR A p)) (reifySR (evalSR B p))
evalSR (con tcn)   p = refl≡β _
\end{code}

Identity SREnv

\begin{code}
idSR : ∀{Φ} → SREnv ` (idEnv Φ)
idSR = reflectSR ∘ refl≡β ∘ `
\end{code}

Soundness Result

\begin{code}
soundness : ∀ {Φ J} → (A : Φ ⊢⋆ J) → A ≡β embNf (nf A)
soundness A = trans≡β (≡2β (sym (subst-id A))) (reifySR (evalSR A idSR)) 
\end{code}
