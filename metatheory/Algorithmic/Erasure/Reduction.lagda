\begin{code}
module Algorithmic.Erasure.Reduction where
\end{code}

\begin{code}
open import Function

open import Type
open import Type.BetaNormal
open import Algorithmic as A
import Algorithmic.Reduction as A
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Algorithmic.Erasure.RenamingSubstitution
import Untyped.Reduction as U
import Untyped.RenamingSubstitution as U
open import Builtin
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Untyped
open import Builtin.Signature Ctx⋆ Kind
  ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Type.BetaNBE.RenamingSubstitution

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (map)
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Data.Unit
\end{code}

\begin{code}
eraseVal : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t : Γ ⊢ A}
  → A.Value t → U.Value (erase t)
eraseVal (A.V-ƛ {N = t})      = U.V-ƛ (erase t)
eraseVal (A.V-Λ v)            = eraseVal v
eraseVal (A.V-wrap v)         = eraseVal v
eraseVal (A.V-con {Γ = Γ} cn) = U.V-con (eraseTC {Γ = Γ} cn)

eraseVTel : ∀ {Φ} Γ Δ
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (As : List (Δ ⊢Nf⋆ *))
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.VTel (len Γ) (eraseTel tel)
eraseVTel Γ Δ σ []       tel        vtel        = _ 
eraseVTel Γ Δ σ (A ∷ As) (t ,, tel) (v ,, vtel) =
  eraseVal v ,, eraseVTel Γ Δ σ As tel vtel 
\end{code}

\begin{code}
erase-BUILTIN : ∀ bn → let Δ ,, As ,, X = SIG bn in
  ∀{Φ}(Γ : Ctx Φ)
  → (σ : ∀{K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.BUILTIN
      bn
      (eraseTel tel)
      (eraseVTel
        Γ
        Δ
        σ
        As
        tel
        vtel)
    ≡ erase (A.BUILTIN bn σ tel vtel)
erase-BUILTIN addInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN subtractInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN multiplyInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN divideInteger Γ σ tel vtel = {!!}
erase-BUILTIN quotientInteger Γ σ tel vtel = {!!}
erase-BUILTIN remainderInteger Γ σ tel vtel = {!!}
erase-BUILTIN modInteger Γ σ tel vtel = {!!}
erase-BUILTIN lessThanInteger Γ σ tel vtel = {!!}
erase-BUILTIN lessThanEqualsInteger Γ σ tel vtel = {!!}
erase-BUILTIN greaterThanInteger Γ σ tel vtel = {!!}
erase-BUILTIN greaterThanEqualsInteger Γ σ tel vtel = {!!}
erase-BUILTIN equalsInteger Γ σ tel vtel = {!!}
erase-BUILTIN concatenate Γ σ tel vtel = {!!}
erase-BUILTIN takeByteString Γ σ tel vtel = {!!}
erase-BUILTIN dropByteString Γ σ tel vtel = {!!}
erase-BUILTIN sha2-256 Γ σ tel vtel = {!!}
erase-BUILTIN sha3-256 Γ σ tel vtel = {!!}
erase-BUILTIN verifySignature Γ σ tel vtel = {!!}
erase-BUILTIN equalsByteString Γ σ tel vtel = {!!}

erase-reconstTel : ∀{Φ Γ Δ As} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : A.Tel Γ Δ σ Bs)
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : A.Tel Γ Δ σ Ds)
    → eraseTel (A.reconstTel Bs Ds σ telB t' p tel')
      ≡
      eraseTel telB ++ erase t' ∷ eraseTel tel'
erase-reconstTel []       Ds σ telB        t' refl tel' = refl
erase-reconstTel (B ∷ Bs) Ds σ (t ,, telB) t' refl tel' =
  cong (erase t ∷_) (erase-reconstTel Bs Ds σ telB t' refl tel')
    
\end{code}

\begin{code}
erase—→ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t t' : Γ ⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'
erase—→ (A.ξ-Λ p)                                       = erase—→ p
erase—→ (A.ξ-·₁ {M = M} p)                              = map
  U.ξ-·₁
  (cong (_· erase M))
  (erase—→ p)
erase—→ (A.ξ-·₂ {V = V} p q)                            = map
  (U.ξ-·₂ (eraseVal p))
  ((cong (erase V ·_)))
  (erase—→ q)
erase—→ (A.ξ-·⋆ p)                                      = erase—→ p
erase—→ (A.β-ƛ {x = x}{N = N}{W = W})                   =
  inj₁ (subst ((ƛ x (erase N) · erase W) U.—→_) (lem[] N W) U.β-ƛ)
erase—→ (A.β-Λ {N = N}{A = A})                          =
  inj₂ (lem[]⋆ N A)
erase—→ A.β-wrap1                                       = inj₂ refl
erase—→ (A.ξ-unwrap1 p)                                 = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ (A.β-builtin bn σ tel vtel)                     = inj₁ (subst
  (builtin bn (eraseTel tel) U.—→_)
  (erase-BUILTIN bn _ σ tel vtel)
  (U.β-builtin (eraseTel tel) (eraseVTel _ _ σ _ tel vtel)))
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel p q) with erase—→ p
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel {t' = t'} p q) | inj₁ x = inj₁ (subst
    (builtin bn (eraseTel tel) U.—→_)
    (cong (builtin bn) (sym (erase-reconstTel Bs Ds σ telB t' q telD)))
    (U.ξ-builtin
      bn
      (eraseTel tel)
      (eraseVTel _ _ σ _ _ vtel)
      x
      (eraseTel telD)
      (eraseTel telB ++ erase t' ∷ eraseTel telD) refl))
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel {t' = t'} p q) | inj₂ y
  = inj₂ (cong (builtin bn) (trans {!!} (sym (erase-reconstTel Bs Ds σ telB t' q telD))))
\end{code}
