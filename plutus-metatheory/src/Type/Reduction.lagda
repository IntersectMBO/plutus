\begin{code}
module Type.Reduction where
\end{code}

Right now this file is not used in other things. We compute types via
NBE. Instead, it acts as a warmup to understanding reduction of terms.

This version of reduction does not compute under binders. The NBE
version does full normalisation.

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

  V-Π : ∀ {Φ K}
    → (N : Φ ,⋆ K ⊢⋆ *)
      ----------------------------
    → Value⋆ (Π N)

  _V-⇒_ : ∀ {Φ} {S : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → Value⋆ S
    → Value⋆ T
      -----------------------------------
    → Value⋆ (S ⇒ T)

  V-ƛ : ∀ {Φ K J}
    → (N : Φ ,⋆ K ⊢⋆ J)
      -----------------------------
    → Value⋆ (ƛ N)

  N- : ∀ {Φ K} {N : Φ ⊢⋆ K}
    → Neutral⋆ N
      ----------
    → Value⋆ N

  V-con : ∀{Φ}
    → (tcn : TyCon)
      ------------------
    → Value⋆ {Γ = Φ} (con tcn)

data Neutral⋆ where
  N-μ1 : ∀ {Φ K}
      ----------------------------
    → Neutral⋆ (μ1 {Φ}{K})
    
  N-· :  ∀ {Φ K J} {N : Φ ⊢⋆ K ⇒ J}{V : Φ ⊢⋆ K}
   → Neutral⋆ N
   → Value⋆ V
   → Neutral⋆ (N · V)
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
    → Value⋆ V
    → M —→⋆ M′
      --------------
    → V · M —→⋆ V · M′

  β-ƛ : ∀ {Γ K J} {N : Γ ,⋆ K ⊢⋆ J} {W : Γ ⊢⋆ K}
    → Value⋆ W
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
progress⋆ : ∀ {K} → (M : ∅ ⊢⋆ K) → Progress⋆ M
progress⋆ (` ())
progress⋆ μ1      = done (N- N-μ1)
progress⋆ (Π M)   = done (V-Π M)
progress⋆ (M ⇒ N) with progress⋆ M
progress⋆ (M ⇒ N) | step p = step (ξ-⇒₁ p)
progress⋆ (M ⇒ N) | done VM with progress⋆ N
progress⋆ (M ⇒ N) | done VM | step q  = step (ξ-⇒₂ VM q)
progress⋆ (M ⇒ N) | done VM | done VN = done (VM V-⇒ VN)
progress⋆ (ƛ M)   = done (V-ƛ M)
progress⋆ (M · N)  with progress⋆ M
...                    | step p = step (ξ-·₁ p)
...                    | done vM with progress⋆ N
...                               | step p = step (ξ-·₂ vM p)
progress⋆ (.(ƛ _) · N) | done (V-ƛ M) | done vN = step (β-ƛ vN)
progress⋆ (M · N) | done (N- M') | done vN = done (N- (N-· M' vN))
progress⋆ (con tcn) = done (V-con tcn)
\end{code}

\begin{code}
open import Relation.Nullary
open import Data.Product
open import Data.Empty

mutual
  -- doesn't need to be mutual, we could separately prove that a type
  -- cannot be both a value and a neutral which would take care of the
  -- ξ-·₂ case of notbothN
  notbothN : ∀{Φ K}(A : Φ ⊢⋆ K) → ¬ (Neutral⋆ A × (Σ (Φ ⊢⋆ K) (A —→⋆_)))
  notbothN .(_ · _) (N-· N A , .(_ · _) , ξ-·₁ p) = notbothN _ (N , _ , p)
  notbothN .(_ · _) (N-· N A , .(_ · _) , ξ-·₂ V p) = notboth _ (A , _ , p)
  
  notboth : ∀{Φ K}(A : Φ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (Φ ⊢⋆ K) (A —→⋆_)))
  notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₁ p) = notboth _ (V , _ , p) 
  notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₂ _ p) = notboth _ (W , _ , p)
  notboth ._ (N- N , _ , p) = notbothN _ (N , _ , p)

det : ∀{Φ K}{A A' A'' : Φ ⊢⋆ K}(p : A —→⋆ A')(q : A —→⋆ A'') → A' ≡ A''
det (ξ-⇒₁ p) (ξ-⇒₁ q) = cong (_⇒ _) (det p q)
det (ξ-⇒₁ p) (ξ-⇒₂ v q) = ⊥-elim (notboth _ (v , _ , p))
det (ξ-⇒₂ v p) (ξ-⇒₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-⇒₂ v p) (ξ-⇒₂ w q) = cong (_ ⇒_) (det p q)
det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ v q) = ⊥-elim (notboth _ (v , _ , p))
det (ξ-·₁ ()) (β-ƛ v)
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (notboth _ (w , _ , p))
det (β-ƛ v) (ξ-·₁ ())
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (notboth _ (v , _ , q))
det (β-ƛ v) (β-ƛ w) = refl
\end{code}
