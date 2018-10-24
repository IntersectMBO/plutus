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
\end{code}

The Soundness Relation (SR) is a Kripke logical relation between terms
and values. It is defined by induction on kinds. it says that a term
is related to a value if when we reach ground type (# or *) then the
term is beta-eta-equal to the result of reifying the value.

\begin{code}
SR : ∀{Γ} K → Γ ⊢⋆ K → Val Γ K → Set
SR #       t v        = t ≡β embNf (reify v)
SR *       t v        = t ≡β embNf (reify v)
SR (K ⇒ J) t (inj₁ n) = t ≡β embNeN n
SR (K ⇒ J) t (inj₂ f) = Σ (_ ,⋆ K ⊢⋆ J) λ t' →
  (t ≡β ƛ t') -- this bit of indirection is needed as we have only β not βη
  ×
  ∀{Δ}
    → (ρ : Ren _ Δ)
    → {u : Δ ⊢⋆ K}
    → {v : Val Δ K}
    → SR K u v
      ------------------------------------------------------
    → SR J (rename ρ (ƛ t') · u) (renameVal ρ (inj₂ f) ·V v)
\end{code}

\begin{code}
reflectSR : ∀{Γ K}{t : Γ ⊢⋆ K}{n : Γ ⊢NeN⋆ K}
  → t ≡β embNeN n
    ------------------
  → SR K t (reflect n)
reflectSR {K = #}     p = p
reflectSR {K = *}     p = p
reflectSR {K = K ⇒ J} p = p

reifySR : ∀{Γ K}{t : Γ ⊢⋆ K}{v : Val Γ K}
  → SR K t v
    --------------------
  → t ≡β embNf (reify v)
reifySR {K = *}                  p            = p
reifySR {K = #}                  p            = p
reifySR {K = K ⇒ J} {t} {inj₁ n} p            = p
reifySR {K = K ⇒ J} {t} {inj₂ f} (t' , p , q) =
  trans≡β p (substEq (λ t → ƛ t ≡β ƛ (embNf (reify (f S fresh))))
                     (trans (sym (subst-rename t'))
                            (trans (subst-cong (λ { Z → refl
                                                  ; (S x) → refl}) t')
                                   (subst-id t')))
                     (ƛ≡β (trans≡β (sym≡β (β≡β _ _))
                                   (reifySR (q S (reflectSR (refl≡β (` Z))))))))
\end{code}

Lifting SR from ⊢⋆/Val to Sub/Env

\begin{code}
SRSubEnv : ∀{Γ Δ} → Sub Γ Δ → Env Γ Δ → Set
SRSubEnv {Γ} σ η = ∀{K}(x : Γ ∋⋆ K) → SR K (σ x) (η x)
\end{code}

Cons for SRSubEnv

\begin{code}
SR,,⋆ : ∀{Γ Δ}{σ : Sub Γ Δ}{η : Env Γ Δ}
  → SRSubEnv σ η
  → ∀{K}{t : Δ ⊢⋆ K}{v : Val Δ K}
  → SR K t v
  → SRSubEnv (subst-cons σ t) (η ,,⋆ v)
SR,,⋆ p q Z     = q
SR,,⋆ p q (S x) = p x
\end{code}

renaming for SR

\begin{code}
renSR : ∀{Γ Δ}(ρ : Ren Γ Δ){K}{t : Γ ⊢⋆ K}{v : Val Γ K}
  → SR K t v
    ---------------------------------
  → SR K (rename ρ t) (renameVal ρ v)
renSR ρ {#}{t}{n} p = 
  substEq (rename ρ t ≡β_) (sym (rename-embNf ρ n)) (rename≡β ρ p)
renSR ρ {*}{t}{n} p = 
  substEq (rename ρ t ≡β_) (sym (rename-embNf ρ n)) (rename≡β ρ p)
renSR ρ {K ⇒ J} {t} {inj₁ n} p rewrite rename-embNeN ρ n = rename≡β ρ p  
renSR ρ {K ⇒ J} {t} {inj₂ f} (t' , p , q) =
  rename (ext ρ) t'
  ,
  rename≡β ρ p
  ,
  λ ρ' {u}{v} r → substEq (λ t → SR J (ƛ t · u) (f (ρ' ∘ ρ) v))
                          (trans (rename-cong ext-comp t') (rename-comp t'))
                          (q (ρ' ∘ ρ) r)
\end{code}

Extending via exts is the same the same as weakening and cons on ` Z

\begin{code}
exts-subst-cons : ∀{Γ Δ K J}(σ : Sub Γ Δ)(x : Γ ,⋆ J ∋⋆ K)
  → exts σ x ≡ subst-cons (weaken ∘ σ) (` Z) x
exts-subst-cons σ Z = refl
exts-subst-cons σ (S x) = refl
\end{code}

SRSubEnv is closed under (pointwise) equality of environments

\begin{code}
substSREnv : ∀{Γ Δ}{σ σ' : Sub Γ Δ}
  → (∀{K}(x : Γ ∋⋆ K) → σ x ≡ σ' x)
  → {η : Env Γ Δ}
  → SRSubEnv σ η
  → SRSubEnv σ' η
substSREnv p q x rewrite sym (p x) = q x
\end{code}

SRSubEnv is closed under exts/extending the env
(note: would this be cleaner if we used exte?)

\begin{code}
SRweak : ∀{Γ Δ}{σ : Sub Γ Δ}{η : Env Γ Δ}
  → SRSubEnv σ η
  → ∀ {K}
    -------------------------------------------------------
  → SRSubEnv (exts σ) ((renameVal S ∘ η) ,,⋆ fresh {σ = K})
SRweak p = substSREnv (sym ∘ exts-subst-cons _)
                      (SR,,⋆ (renSR S ∘ p) (reflectSR (refl≡β (` Z)))) 
\end{code}

SR is closed under ≡β

\begin{code}
substSR : ∀{Γ K}{t t' : Γ ⊢⋆ K}
  → t' ≡β t
  → {v : Val Γ K}
  → SR K t v
    ---------------------------
  → SR K t' v
substSR {K = #}     p          q            = trans≡β p q
substSR {K = *}     p          q            = trans≡β p q
substSR {K = K ⇒ J} p {inj₁ n} q            = trans≡β p q
substSR {K = K ⇒ J} p {inj₂ f} (t' , q , r) = _ , trans≡β p q , r
\end{code}

SR is closed under ·V

\begin{code}
SRApp : ∀{Γ K J}
  → {t : Γ ⊢⋆ (K ⇒ J)}
  → {f : Val Γ (K ⇒ J)}
  → SR (K ⇒ J) t f
  → {u : Γ ⊢⋆ K}
  → {v : Val Γ K}
  → SR K u v
    ---------------------
  → SR J (t · u) (f ·V v)
SRApp {f = inj₁ n} p            q =
  reflectSR (·≡β (reflectSR p) (reifySR q))
SRApp {f = inj₂ f} (t' , p , q) r =
  substSR (·≡β (substEq
                 (λ t' → _ ≡β ƛ t')
                 (trans (sym (rename-id t')) (rename-cong (sym ∘ ext-id) t'))
                 p)
               (refl≡β _))
          (q id r)
\end{code}

Fundamental Theorem of Logical Relations for SR

\begin{code}
evalSR : ∀{Γ Δ K}(t : Γ ⊢⋆ K){σ : Sub Γ Δ}{η : Env Γ Δ}
  → SRSubEnv σ η
  → SR K (subst σ t) (eval t η)
evalSR (` x)   p = p x
evalSR (Π B)   p = Π≡β (evalSR B (SRweak p))
evalSR (A ⇒ B) p = ⇒≡β (evalSR A p) (evalSR B p)
evalSR {K = K ⇒ J} (ƛ B){σ}{η} p =
  subst (exts σ) B
  ,
  refl≡β _
  ,
  λ ρ {u}{v} q → substSR
    (β≡β _ _)
    (substEq (λ t → SR J t (eval B ((renameVal ρ ∘ η) ,,⋆ v)))
             (trans (trans (subst-cong (λ
               { Z → refl
               ; (S x) → trans (trans (sym (subst-id (rename ρ (σ x))))
                                      (sym (subst-rename (σ x))))
                               (subst-rename (σ x))}) B)
                           (subst-comp B))
                    (subst-rename (subst (exts σ) B)))
             (evalSR B (SR,,⋆ (renSR ρ ∘ p) q)) )
evalSR (A · B)     p = SRApp (evalSR A p) (evalSR B p)
evalSR (μ B)       p = reflectSR (μ≡β (reifySR (evalSR B (SRweak p))))
evalSR (size⋆ n)   p = refl≡β _
evalSR (con tcn s) p = con≡β (evalSR s p)
\end{code}

Identity SRSubEnv

\begin{code}
idSR : ∀{Γ} → SRSubEnv ` (idEnv Γ)
idSR x = reflectSR (refl≡β (` x))
\end{code}

Soundness Result

\begin{code}
soundness : ∀ {Φ J} → (t : Φ ⊢⋆ J) → t ≡β embNf (nf t)
soundness t =
  substEq (λ t' → t' ≡β embNf (nf t)) (subst-id t) (reifySR (evalSR t idSR))
\end{code}
