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

\begin{code}
R : ∀{Γ} K → Γ ⊢⋆ K → Val Γ K → Set
R #    t v = t ≡β embNf (reify v)
R *       t v = t ≡β embNf (reify v)
R (K ⇒ J) t (inj₁ n) = t ≡β embNeN n
R (K ⇒ J) t (inj₂ f) = Σ (_ ,⋆ K ⊢⋆ J) λ t' → (t ≡β ƛ t') × ∀{Δ}(ρ : Ren _ Δ){u : Δ ⊢⋆ K}{v : Val Δ K}
  → R K u v  → R J (rename ρ (ƛ t') · u) (renval ρ (inj₂ f) ·V v)
\end{code}

\begin{code}
sreflect : ∀{Γ K}{t : Γ ⊢⋆ K}{n : Γ ⊢NeN⋆ K}
  → t ≡β embNeN n
  → R K t (reflect n)
sreflect {K = #}  p = p
sreflect {K = *}     p = p
sreflect {K = K ⇒ J} p = p

sreify : ∀{Γ K}{t : Γ ⊢⋆ K}{v : Val Γ K}
  → R K t v
  → t ≡β embNf (reify v)
sreify {K = *}     p = p
sreify {K = #}  p = p
sreify {K = K ⇒ J} {t} {inj₁ n} p = p
sreify {K = K ⇒ J} {t} {inj₂ f} (t' , p , q) =
  trans≡β p (substEq (λ t → ƛ t ≡β ƛ (embNf (reify (f S fresh))))
                     (trans (sym (subst-rename t'))
                            (trans (subst-cong (λ { Z → refl ; (S x) → refl}) t')
                                   (subst-id t')))
                     (ƛ≡β (trans≡β (sym≡β (β≡β _ _)) (sreify {K = J} (q S (sreflect (refl≡β (` Z))))))))
\end{code}

\begin{code}

RSubEnv : ∀{Γ Δ} → Sub Γ Δ → Env Γ Δ → Set
RSubEnv {Γ} σ η = ∀{K}(x : Γ ∋⋆ K) → R K (σ x) (η x)
\end{code}

\begin{code}
R,,⋆ : ∀{Γ Δ}{σ : Sub Γ Δ}{η : Env Γ Δ}
  → RSubEnv σ η
  → ∀{K}{t : Δ ⊢⋆ K}{v : Val Δ K}
  → R K t v
  → RSubEnv (subst-cons σ t) (η ,,⋆ v)
R,,⋆ p q Z     = q
R,,⋆ p q (S x) = p x
\end{code}

\begin{code}
renR : ∀{Γ Δ}(ρ : Ren Γ Δ){K}{t : Γ ⊢⋆ K}{v : Val Γ K}
  → R K t v
  → R K (rename ρ t) (renval ρ v)
renR ρ {#}{t}{n} p = 
  substEq (rename ρ t ≡β_) (sym (rename-embNf ρ n)) (rename≡β ρ p)
renR ρ {*}{t}{n} p = 
  substEq (rename ρ t ≡β_) (sym (rename-embNf ρ n)) (rename≡β ρ p)
renR ρ {K ⇒ J} {t} {inj₁ n} p rewrite rename-embNeN ρ n = rename≡β ρ p  
renR ρ {K ⇒ J} {t} {inj₂ f} (t' , p , q) =
  rename (ext ρ) t'
  ,
  rename≡β ρ p
  ,
  λ ρ' {u}{v} r → substEq (λ t → R J (ƛ t · u) (f (ρ' ∘ ρ) v))
                          (trans (rename-cong ext-comp t') (rename-comp t'))
                          (q (ρ' ∘ ρ) r)
\end{code}

\begin{code}
lemma : ∀{Γ Δ K J}(σ : Sub Γ Δ)(x : Γ ,⋆ J ∋⋆ K)
  → exts σ x ≡ subst-cons (rename S ∘ σ) (` Z) x
lemma σ Z = refl
lemma σ (S x) = refl
\end{code}

\begin{code}
substREnv : ∀{Γ Δ}{σ σ' : Sub Γ Δ}
  → (∀{K}(x : Γ ∋⋆ K) → σ x ≡ σ' x)
  → {η : Env Γ Δ}
  → RSubEnv σ η
  → RSubEnv σ' η
substREnv p q x rewrite sym (p x) = q x
\end{code}

\begin{code}
Rweak : ∀{Γ Δ}{σ : Sub Γ Δ}{η : Env Γ Δ}
  → RSubEnv σ η
  → ∀ K
  → RSubEnv (exts σ) ((renval S ∘ η) ,,⋆ fresh {σ = K})
Rweak {σ = σ} p K = substREnv (sym ∘ lemma σ) (R,,⋆ (renR S ∘ p) (sreflect (refl≡β (` (Z {J = K}))))) 
\end{code}

\begin{code}
substR : ∀{Γ K}{t t' : Γ ⊢⋆ K}
  → t' ≡β t
  → {v : Val Γ K}
  → R K t v
  → R K t' v
substR {K = #}   p q = trans≡β p q
substR {K = *}      p q = trans≡β p q
substR {K = K ⇒ J} p {inj₁ n} q = trans≡β p q
substR {K = K ⇒ J} p {inj₂ f} (t' , q , r) = _ , trans≡β p q , r
\end{code}

\begin{code}
RApp : ∀{Γ K J}
  → {t : Γ ⊢⋆ (K ⇒ J)}
  → {f : Val Γ (K ⇒ J)}
  → R (K ⇒ J) t f
  → {u : Γ ⊢⋆ K}
  → {v : Val Γ K}
  → R K u v 
  → R J (t · u) (f ·V v)
RApp {t = t} {inj₁ n} p {u} {v} q = sreflect (·≡β (sreflect p) (sreify q))
RApp {t = t} {inj₂ f} (t' , p , q) {u} {v} r =
  substR (·≡β (substEq (λ t' → t ≡β ƛ t')
                       (trans (sym (rename-id t')) (rename-cong (sym ∘ ext-id) t'))
                       p)
              (refl≡β u))
         (q id r)
\end{code}

\begin{code}
sfund : ∀{Γ Δ K}(t : Γ ⊢⋆ K){σ : Sub Γ Δ}{η : Env Γ Δ}
  → RSubEnv σ η
  → R K (subst σ t) (eval t η)
sfund (` x)   p = p x
sfund (Π B)   p = Π≡β (sfund B (Rweak p _))
sfund (A ⇒ B) p = ⇒≡β (sfund A p) (sfund B p)
sfund {K = K ⇒ J} (ƛ B){σ}{η} p =
  subst (exts σ) B
  ,
  refl≡β _
  ,
  λ ρ {u}{v} q → substR
    (β≡β _ _)
    (substEq (λ t → R J t (eval B ((renval ρ ∘ η) ,,⋆ v)))
             (trans (trans (subst-cong (λ { Z → refl
                                          ; (S x) → trans (trans (sym (subst-id (rename ρ (σ x))))
                                                                 (sym (subst-rename (σ x))))
                                                          (subst-rename (σ x))})
                                       B)
                           (subst-comp B))
                    (subst-rename (subst (exts σ) B)))
             (sfund B (R,,⋆ (renR ρ ∘ p) q)) )
sfund (A · B) p = RApp (sfund A p) (sfund B p)
sfund (μ B)   p = sreflect (μ≡β (sreify (sfund B (Rweak p _))))
sfund (size⋆ n)   p = refl≡β _
sfund (con tcn s) p = con≡β (sfund s p)
\end{code}

\begin{code}
idR : ∀{Γ} → RSubEnv ` (idEnv Γ)
idR x = sreflect (refl≡β (` x))
\end{code}

\begin{code}
soundness : ∀ {Φ J} → (t : Φ ⊢⋆ J) → t ≡β embNf (nf t)
soundness t = substEq (λ t' → t' ≡β embNf (nf t)) (subst-id t) (sreify (sfund t idR))
\end{code}
