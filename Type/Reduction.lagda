\begin{code}
module Type.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
\end{code}

## Values

\begin{code}
data Neutral⋆ : ∀ {Γ K} → Γ ⊢⋆ K → Set
data Value⋆   : ∀ {Γ K} → Γ ⊢⋆ K → Set where

  V-Π_ : ∀ {Φ K} {N : Φ ,⋆ K ⊢⋆ *}
    → Value⋆ N
      ----------------------------
    → Value⋆ (Π N)

  _V-⇒_ : ∀ {Φ} {S : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → Value⋆ S
    → Value⋆ T
      -----------------------------------
    → Value⋆ (S ⇒ T)

  V-ƛ_ : ∀ {Φ K J} {N : Φ ,⋆ K ⊢⋆ J}
      -----------------------------
    → Value⋆ (ƛ N)

  N- : ∀ {Φ K} {N : Φ ⊢⋆ K}
    → Neutral⋆ N
      ----------
    → Value⋆ N

  V-size : ∀{Φ}
    → {n : Nat}
      --------------------
    → Value⋆ (size⋆ {Φ} n)

  V-con : ∀{Φ}
    → {tcn : TyCon}
    → {s : Φ ⊢⋆ #}
    → Value⋆ s
      ------------------
    → Value⋆ (con tcn s)

-- as we only prove progress in the empty context we have no stuck
-- applications of a variable to an argument outside of a
-- binder. However, due to allowing μ to appear at arbitrary kind we
-- can have terms such as "μ X · Y" which are stuck and hence we
-- introduce neutral terms.

data Neutral⋆ where
  N-μ1 : ∀ {Φ K}
      ----------------------------
    → Neutral⋆ (μ1 {Φ}{K})
    
  N-· :  ∀ {Φ K J} {N : Φ ⊢⋆ K ⇒ J}{V : Φ ⊢⋆ K}
   → Neutral⋆ N
   → Value⋆ V
   → Neutral⋆ (N · V)

  N-` : ∀ {Φ K}{α : Φ ∋⋆ K} → Neutral⋆ (` α)
\end{code}

## Intrinsically Kind Preserving Type Reduction

\begin{code}
infix 2 _—→⋆_
infix 2 _—↠⋆_

data _—→⋆_ : ∀ {Γ J} → (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where
  ξ-⇒₁ : ∀ {Φ} {S S' : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → S —→⋆ S'
      -----------------------------------
    → S ⇒ T —→⋆ S' ⇒ T

  ξ-⇒₂ : ∀ {Φ} {S : Φ ⊢⋆ *} {T T' : Φ ⊢⋆ *}
    → Value⋆ S
    → T —→⋆ T'
      -----------------------------------
    → S ⇒ T —→⋆ S ⇒ T'

  ξ-·₁ : ∀ {Γ K J} {L L′ : Γ ⊢⋆ K ⇒ J} {M : Γ ⊢⋆ K}
    → L —→⋆ L′
      -----------------
    → L · M —→⋆ L′ · M

  ξ-·₂ : ∀ {Γ K J} {V : Γ ⊢⋆ K ⇒ J} {M M′ : Γ ⊢⋆ K}
 --   → Value⋆ V
    → M —→⋆ M′
      --------------
    → V · M —→⋆ V · M′

  ξ-con : ∀{Φ}
    → {tcn : TyCon}
    → {s s' : Φ ⊢⋆ #}
    → s —→⋆ s'
      ------------------
    → con tcn s —→⋆ con tcn s'

  ξ-Π : ∀ {Γ K} {M M′ : Γ ,⋆ K ⊢⋆ *}
    → M —→⋆ M′
      -----------------
    → Π M —→⋆ Π M′

  ξ-ƛ : ∀ {Γ K J} {M M′ : Γ ,⋆ K ⊢⋆ J}
    → M —→⋆ M′
      -----------------
    → ƛ M —→⋆ ƛ M′



  β-ƛ : ∀ {Γ K J} {N : Γ ,⋆ K ⊢⋆ J} {W : Γ ⊢⋆ K}
 --   → Value⋆ W
      -------------------
    → ƛ N · W —→⋆ N [ W ]
\end{code}

\begin{code}
data _—↠⋆_ {J Γ} :  (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where

  refl—↠⋆ : ∀{M}
      --------
    → M —↠⋆ M

  trans—↠⋆ : {L : Γ ⊢⋆ J} {M N : Γ ⊢⋆ J}
    → L —→⋆ M
    → M —↠⋆ N
      ---------
    → L —↠⋆ N

ƛ—↠⋆ : ∀{Γ K J}{M N : Γ ,⋆ K ⊢⋆ J} → M —↠⋆ N → ƛ M —↠⋆ ƛ N
ƛ—↠⋆ refl—↠⋆          = refl—↠⋆
ƛ—↠⋆ (trans—↠⋆ p q) = trans—↠⋆ (ξ-ƛ p) (ƛ—↠⋆ q)

Π—↠⋆ : ∀{Γ K}{M N : Γ ,⋆ K ⊢⋆ *} → M —↠⋆ N → Π M —↠⋆ Π N
Π—↠⋆ refl—↠⋆          = refl—↠⋆
Π—↠⋆ (trans—↠⋆ p q) = trans—↠⋆ (ξ-Π p) (Π—↠⋆ q)

ξ-·₁' : ∀ {Γ K J} {L L′ : Γ ⊢⋆ K ⇒ J} {M : Γ ⊢⋆ K}
  → L —↠⋆ L′
    -----------------
  → L · M —↠⋆ L′ · M
ξ-·₁' refl—↠⋆ = refl—↠⋆
ξ-·₁' (trans—↠⋆ p q) = trans—↠⋆ (ξ-·₁ p) (ξ-·₁' q)

ξ-·₂' : ∀ {Γ K J} {L : Γ ⊢⋆ K ⇒ J} {M M′ : Γ ⊢⋆ K}
  → Value⋆ L
  → M —↠⋆ M′
    -----------------
  → L · M —↠⋆ L · M′
ξ-·₂' _ refl—↠⋆ = refl—↠⋆
ξ-·₂' VL (trans—↠⋆ p q) = trans—↠⋆ (ξ-·₂ p) (ξ-·₂' VL q)

ξ-⇒₁' : ∀ {Φ} {S S' : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → S —↠⋆ S'
      -----------------------------------
    → (S ⇒ T) —↠⋆ (S' ⇒ T)
ξ-⇒₁' refl—↠⋆        = refl—↠⋆
ξ-⇒₁' (trans—↠⋆ p q) = trans—↠⋆ (ξ-⇒₁ p) (ξ-⇒₁' q)

ξ-⇒₂' : ∀ {Φ} {S : Φ ⊢⋆ *} {T T' : Φ ⊢⋆ *}
    → Value⋆ S
    → T —↠⋆ T'
      -----------------------------------
    → (S ⇒ T) —↠⋆ (S ⇒ T')
ξ-⇒₂' VS refl—↠⋆ = refl—↠⋆
ξ-⇒₂' VS (trans—↠⋆ p q) = trans—↠⋆ (ξ-⇒₂ VS p) (ξ-⇒₂' VS q)

ξ-con' : ∀{Φ}
  → {tcn : TyCon}
  → {s s' : Φ ⊢⋆ #}
  → s —↠⋆ s'
    ------------------
  → con tcn s —↠⋆ con tcn s'
ξ-con' refl—↠⋆          = refl—↠⋆
ξ-con' (trans—↠⋆ p q) = trans—↠⋆ (ξ-con p) (ξ-con' q)

-- like concatenation for lists
-- the ordinary trans is like cons
trans—↠⋆' : ∀{Γ J}{L M N : Γ ⊢⋆ J} → L —↠⋆ M → M —↠⋆ N → L —↠⋆ N
trans—↠⋆' refl—↠⋆ p = p
trans—↠⋆' (trans—↠⋆ p q) r = trans—↠⋆ p (trans—↠⋆' q r)
\end{code}

\begin{code}
data Progress⋆ {Γ K} (M : Γ ⊢⋆ K) : Set where
  step : ∀ {N : Γ ⊢⋆ K}
    → M —→⋆ N
      -------------
    → Progress⋆ M
  done :
      Value⋆ M
      ----------
    → Progress⋆ M
\end{code}

\begin{code}
progress⋆ : ∀ {Γ K} → (M : Γ ⊢⋆ K) → Progress⋆ M
progress⋆ (` α) = done (N- N-`)
progress⋆ μ1      = done (N- N-μ1)
progress⋆ (Π M)   with progress⋆ M
progress⋆ (Π M) | step p = step (ξ-Π p)
progress⋆ (Π M) | done p = done (V-Π p)
progress⋆ (M ⇒ N) with progress⋆ M
progress⋆ (M ⇒ N) | step p = step (ξ-⇒₁ p)
progress⋆ (M ⇒ N) | done VM with progress⋆ N
progress⋆ (M ⇒ N) | done VM | step q  = step (ξ-⇒₂ VM q)
progress⋆ (M ⇒ N) | done VM | done VN = done (VM V-⇒ VN)
progress⋆ (ƛ M)   = done V-ƛ_
progress⋆ (M · N)  with progress⋆ M
...                    | step p = step (ξ-·₁ p)
...                    | done vM with progress⋆ N
...                                | step p = step (ξ-·₂ p)
progress⋆ (.(ƛ _) · N) | done V-ƛ_ | done vN = step β-ƛ
progress⋆ (M · N) | done (N- M') | done vN = done (N- (N-· M' vN))
progress⋆ (size⋆ n)   = done V-size
progress⋆ (con tcn s) with progress⋆ s
... | step p  = step (ξ-con p)
... | done Vs = done (V-con Vs)

\end{code}

# Renaming and Substitution

\begin{code}
renameNeutral⋆ : ∀ {Φ Ψ}
  → (ρ : Ren Φ Ψ)
  → ∀ {J}{A : Φ ⊢⋆ J}
  → Neutral⋆ A
    ---------------------
  → Neutral⋆ (rename ρ A)

renameValue⋆ : ∀ {Φ Ψ}
  → (ρ : Ren Φ Ψ)
  → ∀ {J}{A : Φ ⊢⋆ J}
  → Value⋆ A
    -------------------
  → Value⋆ (rename ρ A)
renameValue⋆ ρ (V-Π N)   = V-Π renameValue⋆ (ext ρ) N
renameValue⋆ ρ (M V-⇒ N) = renameValue⋆ ρ M V-⇒ renameValue⋆ ρ N
renameValue⋆ ρ V-ƛ_      = V-ƛ_
renameValue⋆ ρ (N- N)    = N- (renameNeutral⋆ ρ N)
renameValue⋆ ρ V-size    = V-size
renameValue⋆ ρ (V-con s) = V-con (renameValue⋆ ρ s)

renameNeutral⋆ ρ N-`       = N-`
renameNeutral⋆ ρ N-μ1      = N-μ1
renameNeutral⋆ ρ (N-· N V) = N-· (renameNeutral⋆ ρ N) (renameValue⋆ ρ V)
\end{code}

\begin{code}
{-
substNeutral⋆ : ∀ {Φ Ψ}
  → (σ : Sub Φ Ψ)
  → ∀ {J}{A : Φ ⊢⋆ J}
  → Neutral⋆ A
    --------------------
  → Neutral⋆ (subst σ A)

substValue⋆ : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → ∀ {J}{A : Φ ⊢⋆ J}
  → Value⋆ A
    -----------------------------
  → Value⋆ (subst σ A)
  
substValue⋆ σ (V-Π N)      = V-Π {!!}
substValue⋆ σ _V-⇒_     = _V-⇒_
substValue⋆ σ V-ƛ_      = V-ƛ_
substValue⋆ σ (N- N)    = N- (substNeutral⋆ σ N)
substValue⋆ σ  V-size   = V-size
substValue⋆ σ (V-con s) = V-con (substValue⋆ σ s)
substNeutral⋆ σ N-` = {!σ _!}
substNeutral⋆ σ N-μ1     = N-μ1
substNeutral⋆ σ (N-· N V) = N-· (substNeutral⋆ σ N) (substValue⋆ σ V)
-}
\end{code}

\begin{code}
rename—→⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : Ren Φ Ψ)
  → A —→⋆ B
    -------------------------
  → rename ρ A —→⋆ rename ρ B
rename—→⋆ ρ (ξ-⇒₁ p)               = ξ-⇒₁ (rename—→⋆ ρ p)
rename—→⋆ ρ (ξ-⇒₂ VM p)            = ξ-⇒₂ (renameValue⋆ ρ VM) (rename—→⋆ ρ p)
rename—→⋆ ρ (ξ-·₁ p)               = ξ-·₁ (rename—→⋆ ρ p)
rename—→⋆ ρ (ξ-·₂ p)               = ξ-·₂ (rename—→⋆ ρ p)
rename—→⋆ ρ (ξ-Π p)                = ξ-Π (rename—→⋆ (ext ρ) p)
rename—→⋆ ρ (ξ-ƛ p)                = ξ-ƛ (rename—→⋆ (ext ρ) p)
rename—→⋆ ρ (β-ƛ {N = M}{W = N})   =
  substEq (λ X → rename ρ ((ƛ M) · N) —→⋆ X)
          (trans (sym (subst-rename M))
                 (trans (subst-cong (rename-subst-cons ρ N) M)
                        (rename-subst M)))
          (β-ƛ {N = rename (ext ρ) M}{W = rename ρ N})
rename—→⋆ ρ (ξ-con p)              = ξ-con (rename—→⋆ ρ p)
\end{code}

\begin{code}
{-
subst—→⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (σ : Sub Φ Ψ)
  → A —→⋆ B
    ----------------------------
  → subst σ A —→⋆ subst σ B
subst—→⋆ σ (ξ-⇒₁ p)               = ξ-⇒₁ (subst—→⋆ σ p)
subst—→⋆ σ (ξ-⇒₂ VM p)            = ξ-⇒₂ (substValue⋆ σ VM) (subst—→⋆ σ p)
subst—→⋆ σ (ξ-·₁ p)               = ξ-·₁ (subst—→⋆ σ p)
subst—→⋆ σ (ξ-·₂ p)             = ξ-·₂ (subst—→⋆ σ p)
subst—→⋆ σ (ξ-Π p)             = ξ-Π (subst—→⋆ (exts σ) p)
subst—→⋆ σ (ξ-ƛ p)             = ξ-ƛ (subst—→⋆ (exts σ) p)
subst—→⋆ σ (β-ƛ {N = M}{W = N}) =
  substEq (λ X → subst σ ((ƛ M) · N) —→⋆ X)
          (trans (sym (subst-comp M))
                 (trans (subst-cong (subst-subst-cons σ N) M)
                        (subst-comp  M)))
          (β-ƛ {N = subst (exts σ) M}{W = subst σ N})
subst—→⋆ ρ (ξ-con p)              = ξ-con (subst—→⋆ ρ p)
-}
\end{code}

\begin{code}
rename—↠⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : Ren Φ Ψ)
  → A —↠⋆ B
    ------------------------------
  → rename ρ A —↠⋆ rename ρ B
rename—↠⋆ ρ refl—↠⋆          = refl—↠⋆
rename—↠⋆ ρ (trans—↠⋆ p q) =
  trans—↠⋆ (rename—→⋆ ρ p) (rename—↠⋆ ρ q)
\end{code}

\begin{code}
{-
subst—↠⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (σ : Sub Φ Ψ)
  → A —↠⋆ B
    ----------------------------
  → subst σ A —↠⋆ subst σ B
subst—↠⋆ σ refl—↠⋆          = refl—↠⋆
subst—↠⋆ σ (trans—↠⋆ p q) =
  trans—↠⋆ (subst—→⋆ σ p) (subst—↠⋆ σ q)
-}
\end{code}


