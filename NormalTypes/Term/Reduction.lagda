\begin{code}
module Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Type
import Type.RenamingSubstitution as ⋆
open import Term
open import Term.RenamingSubstitution
open import Type.Reduction
open import Type.Value
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢V⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ Δ K} {B : Δ ,⋆ K ⊢⋆ *}
    → {vs : Env⋆ ∥ Γ ∥ Δ}
    → {N : Γ ,⋆ K ⊢ eval B (extEnv vs)}
      ----------------
    → Value (Λ {B = B} N)

  V-wrap : ∀{Γ Δ}
    → {A : Δ ,⋆ * ⊢⋆ *}
    → {vs : Env⋆ ∥ Γ ∥ Δ}
    → {M : Γ ⊢ eval A (vs ,⋆ μ A vs )}
      ----------------
    → Value (wrap {B = A} M)

  -- it would be better to push conversions into values somehow
  V-conv : ∀{Γ}{A B : ∥ Γ ∥ ⊢V⋆ *}{L : Γ ⊢ A}(p : A V≡ B)
    → Value L
    → Value (conv p L)

\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢V⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′
    
  ξ-·⋆ : ∀ {Γ Δ K}{B : Δ ,⋆ K ⊢⋆ *}{vs : Env⋆ ∥ Γ ∥ Δ}{L L′ : Γ ⊢ Π B vs}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

{-
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]
-}
{-
  β-Λ : ∀ {Γ}{B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}{N : Γ ,⋆ * ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆
-}

  ξ-unwrap : ∀{Γ Δ}
    → {A : Δ ,⋆ * ⊢⋆ *}
    → {vs : Env⋆ ∥ Γ ∥ Δ}
    → {M M' : Γ ⊢ μ A vs}
    → M —→ M'
    → unwrap M —→ unwrap M'
{-
  β-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M : Γ ⊢ S ⋆.[ μ S ]}    
    → unwrap (wrap S M) —→ M
-}

{-
  ξ-conv₁ : ∀{Γ J}{A B C : ∥ Γ ∥ ⊢V⋆ J}{L : Γ ⊢ A}
    → (p : B —→⋆ A)
    → conv p L —→ L
-}

  ξ-conv₂ : ∀{Γ}{A B : ∥ Γ ∥ ⊢V⋆ *}{L L' : Γ ⊢ A}{p : A V≡ B}
    → L —→ L'
    → conv p L —→ conv p L'
\end{code}

\begin{code}
data _—↠_ {J Γ} : {A : ∥ Γ ∥ ⊢V⋆ J}{A' : ∥ Γ ∥ ⊢V⋆ J} → (Γ ⊢ A) → (Γ ⊢ A') → Set where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∥ Γ ∥ ⊢V⋆ J}{A' : ∥ Γ ∥ ⊢V⋆ J}{A'' : ∥ Γ ∥ ⊢V⋆ J}
    {M : Γ ⊢ A}{M' : Γ ⊢ A}{M'' : Γ ⊢ A''}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
data Progress {A : ∅ ⊢V⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
progress (M · N) | step p = step (ξ-·₁ p)
progress (M · N) | done VM with progress N
progress (M · N) | done VM | step q = step (ξ-·₂ VM q)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step {!!}
progress (.(conv (⇒V≡ _ _) _) · N) | done (V-conv (⇒V≡ p q) VM) | done VN =
  {!!}
progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = {!!}
progress (.(conv ΠV≡ _) ·⋆ A) | done (V-conv ΠV≡ VM) = {!!}
progress (wrap M) = done V-wrap
progress (unwrap M) = {!!}
progress (conv p M) = {!!}

{-
progress : ∀ (A : ∅ ⊢⋆ *) → (M : ∅ ⊢ A) →
  (Value⋆ A × (Value M ⊎ Σ (∅ ⊢ A) λ M' → M —→ M')) -- the type is a a value and either the term is a value or we make a step
  ⊎                                                 -- or
  Σ (∅ ⊢⋆ *) λ A' → A —→⋆ A'                        -- the type makes as step
progress A (` x) = {!!}
progress .(A ⇒ B) (ƛ_ {A = A}{B = B} M) with progress⋆ (A ⇒ B)
progress .(A ⇒ B) (ƛ_ {A = A} {B} M) | inj₁ VM = inj₁ (VM ,, (inj₁ V-ƛ))
progress .(A ⇒ B) (ƛ_ {A = A} {B} M) | inj₂ p = inj₂ p
progress B (M · N) with progress⋆ B
progress B (M · N) | inj₁ VB with progress _ M
progress B (M · N) | inj₁ VB | inj₁ x = {!!}
progress B (M · N) | inj₁ VB | inj₂ y = inj₁ (VB ,, inj₂ {!!})
progress B (M · N) | inj₂ p = inj₂ p
progress .(Π _) (Λ M) = {!!}
progress ._ (M ·⋆ A) = {!!}
progress .(μ A) (wrap A M) = {!!}
progress ._ (unwrap M) = {!!}
progress A (conv p M) = inj₂ (_ ,, p)
-}


-- not possible as for application f a : B where Value⋆ B and f : ∅ ⊢ A ⇒ B
-- we do not know that A is a type value or A => B is a value type
--progress : ∀ (A : ∅ ⊢⋆ *) → Value⋆ A → (M : ∅ ⊢ A) → Value M ⊎ Σ (∅ ⊢ A) λ M' → M —→ M'


{- here we didn't insist that types were values before making a term step
progress : ∀ {A : ∅ ⊢⋆ *} → (M : ∅ ⊢ A) →
  Σ (∅ ⊢⋆ *) λ A' →
     Σ (A' ≡ A) (λ p
     → Σ (∅ ⊢ A') (λ M'
     → Value M' × M ≡ substEq (∅ ⊢_) p M' ⊎ M —→ substEq (∅ ⊢_) p M'))
  ⊎ A —→⋆ A'
progress (` ())
progress (ƛ M) = _ ,, (inj₁ (refl ,, _ ,, (inj₁ (V-ƛ ,, refl))))
progress (M · N) with progress M
progress (M · N) | .(_ ⇒ _) ,, inj₁ (refl ,, .M ,, inj₁ (VM ,, refl)) with progress N
progress (.(ƛ _) · N) | .(_ ⇒ _) ,, inj₁ (refl ,, .(ƛ _) ,, inj₁ (V-ƛ ,, refl)) | A' ,, inj₁ (refl ,, .N ,, inj₁ (VN ,, refl)) =
  _ ,, (inj₁ (refl ,, (_ ,, (inj₂ (β-ƛ VN)))))
progress (_·_ {B = B} M N) | .(_ ⇒ _) ,, inj₁ (refl ,, .M ,, inj₁ (VM ,, refl)) | A' ,, inj₁ (refl ,, N' ,, inj₂ p) =
  B ,, (inj₁ (refl ,, (_ ,, (inj₂ (ξ-·₂ VM p)))))
progress (M · N) | .(_ ⇒ _) ,, inj₁ (refl ,, .M ,, inj₁ (VM ,, refl)) | A' ,, inj₂ p = {!!}
progress (M · N) | .(_ ⇒ _) ,, inj₁ (refl ,, M' ,, inj₂ p) = _ ,, (inj₁ (refl ,, ((M' · N) ,, (inj₂ (ξ-·₁ p)))))
progress (M · N) | A' ,, inj₂ () -- the type can't make a step here
progress (Λ M) = _ ,, (inj₁ (refl ,, _ ,, inj₁ (V-Λ_ ,, refl)))
progress (M ·⋆ A) = {!!}
progress (wrap A M) = _ ,, (inj₁ (refl ,, _ ,, inj₁ (V-wrap ,, refl)))
progress (unwrap M) = {!!}
progress (conv p M) = _ ,, (inj₂ p)
-}
{- this is the version that fails if it hits a conv
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | unhandled-conversion = unhandled-conversion
...                   | step p  = step (ξ-·₁ p)
...                   | done vL with progress M
...                              | unhandled-conversion = unhandled-conversion
...                              | step p  = step (ξ-·₂ vL p)
progress (.(ƛ _) · M) | done V-ƛ | done vM = step (β-ƛ vM)
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
...                    | unhandled-conversion = unhandled-conversion
...                    | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap A M) = done V-wrap
progress (unwrap M) with progress M
...                           | unhandled-conversion = unhandled-conversion
...                           | step p = step (ξ-unwrap p)
progress (unwrap .(wrap _ _)) | done V-wrap = step β-wrap
progress (conv p t) = unhandled-conversion
-}
\end{code}
