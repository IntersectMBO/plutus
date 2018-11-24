\begin{code}
module TermIndexedByNormalType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function
open import Data.Integer renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Type
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Term.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf size⋆
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap1 : ∀{Γ K}
   → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Value (wrap1 pat arg term)

  V-con : ∀{Γ}{n}{tcn : TyCon}
    → (cn : TermCon (con tcn (size⋆ n)))
    → Value (con {Γ} cn)

\end{code}

\begin{code}
open import Data.Unit
open import Data.List hiding ([_])
open import Data.Maybe

VTel : ∀ Γ Δ → (∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K) → List (Δ ⊢Nf⋆ *) → Set
VTel Γ Δ σ [] = ⊤
VTel Γ Δ σ (A ∷ As) = Σ (Γ ⊢ substNf σ A) λ t → Value t × VTel Γ Δ σ As

BUILTIN : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (vtel : VTel Γ Δ σ As)
      -----------------------------
    → Maybe (Γ ⊢ substNf σ C)
BUILTIN addInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  addInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s with boundedI? s (i + j)
... | yes r = just (con (integer s (i + j) r))
... | no ¬r = nothing
BUILTIN bn σ vtel = nothing
\end{code}


## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′
    
  ξ-·⋆ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  β-wrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → {M M' : Γ ⊢ ne (μ1 · pat · arg)}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'

  β-builtin : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As)
      -----------------------------
    → builtin bn σ tel —→ maybe id (error _) (BUILTIN bn σ vtel)


\end{code}

\begin{code}
data _—↠_ {J Γ} : {A : ∥ Γ ∥ ⊢Nf⋆ J}{A' : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Γ ⊢ A' → Set
  where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∥ Γ ∥ ⊢Nf⋆ J}{M  M' M'' : Γ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
  error : Progress M
\end{code}

\begin{code}
data TelProgress
  {Γ}
  {Δ}
  {σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K}
  {As : List (Δ ⊢Nf⋆ *)}
  (tel : Tel Γ Δ σ As)
  : Set where
  done : VTel Γ Δ σ As → TelProgress tel
  step : ∀ Bs Ds
    → VTel Γ Δ σ Bs
    → ∀{C}{t t' : Γ ⊢ substNf σ C}
    → t —→ t'
    → Bs ++ (C ∷ Ds) ≡ As
    → Tel Γ Δ σ Ds
    → TelProgress tel
  error : TelProgress tel
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M

progressTel : ∀ {Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}
  → {As : List (Δ ⊢Nf⋆ *)}
  → (tel : Tel ∅ Δ σ As)
  → TelProgress tel

progressTel {As = []}     _   = done _
progressTel {As = A ∷ As} (t ,, tel) with progress t
progressTel {As = A ∷ As} (t ,, tel) | error   = error
progressTel {As = A ∷ As} (t ,, tel) | step p  = error
progressTel {As = A ∷ As} (t ,, tel) | done vt with progressTel tel
progressTel {As = A ∷ As} (t ,, tel) | done vt | done vtel =
  done (t ,, vt ,, vtel)
progressTel {As = A ∷ As} (t ,, tel) | done vt | step Bs Ds vtel p q tel' =
  error
progressTel {As = A ∷ As} (t ,, tel) | done vt | error = error


progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
...                   | error  = error
progress (M · N)      | step p = step (ξ-·₁ p)
progress (.(ƛ _) · N) | done V-ƛ with progress N
...                              | error  = error
progress (.(ƛ _) · N) | done V-ƛ | step p  = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step (β-ƛ VN)
progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
...               | error  = error
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap1 pat arg term) = done V-wrap1
progress (unwrap1 term)       with progress term
...                     | error  = error
progress (unwrap1 term) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (con (integer s i x))    = done (V-con _)
progress (con (bytestring s b x)) = done (V-con _)
progress (con (TermCon.size s))   = done (V-con _)
progress (builtin bn σ X) with progressTel X
progress (builtin bn σ X) | done VX = step (β-builtin bn σ X VX)
progress (builtin bn σ X) | step Bs Ds vtel p q tel' = error
progress (builtin bn σ X) | error = error
progress (error A)        = error
