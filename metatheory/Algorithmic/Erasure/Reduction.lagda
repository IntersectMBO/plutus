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
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Untyped
open import Builtin.Signature Ctx⋆ Kind
  ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Type.BetaNBE.RenamingSubstitution
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List hiding (map; [_])
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
import Utils as Util
open import Relation.Nullary
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_; _*_)
open import Data.Integer hiding (suc)
import Data.Bool as B
\end{code}

\begin{code}
eraseVal : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t : Γ ⊢ A}
  → A.Value t → U.Value (erase t)
eraseVal (A.V-ƛ {N = t})      = U.V-ƛ (erase t)
eraseVal (A.V-Λ v)            = eraseVal v
eraseVal (A.V-wrap v)         = eraseVal v
eraseVal (A.V-con {Γ = Γ} cn) = U.V-con (eraseTC {Γ = Γ} cn)

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

eraseNe : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t : Γ ⊢ A}
  → A.Neutral t → U.Neutral (erase t)
eraseNe (A.N-` x) = U.N-` (eraseVar x)
eraseNe (A.N-· N M) = U.N-· (eraseNe N) (erase M) 
eraseNe (A.N-·⋆ N A) = eraseNe N
eraseNe (A.N-unwrap1 N) = eraseNe N
eraseNe (A.N-wrap N) = eraseNe N
eraseNe (A.N-Λ N) = eraseNe N
eraseNe (A.N-builtin bn σ tel Bs Ds telB vtel n p telD refl) = U.N-builtin
  bn
  (eraseTel tel)
  (eraseTel telB)
  (eraseNe n)
  (eraseTel telD)
  (erase-reconstTel Bs Ds σ telB _ p telD)

eraseErr : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{e : Γ ⊢ A}
  → A.Error e → U.Error (erase e)
eraseErr A.E-error = U.E-error
eraseErr (A.E-Λ e) = U.E-todo
eraseErr (A.E-·₁ e) = U.E-todo
eraseErr (A.E-·₂ e) = U.E-todo
eraseErr (A.E-·⋆ e) = U.E-todo
eraseErr (A.E-unwrap e) = U.E-todo
eraseErr (A.E-wrap e) = U.E-todo
eraseErr (A.E-builtin bn σ tel Bs Ds telB vtel e p telD) = U.E-todo

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
erase-decIf : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}{X}(p : Dec X)(t f : Γ ⊢ A) →
  Util.decIf p (erase t) (erase f) ≡ erase (Util.decIf p t f)
erase-decIf (yes p) t f = refl
erase-decIf (no ¬p) t f = refl

erase-if : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(b : B.Bool)(t f : Γ ⊢ A) →
  (B.if b then erase t else erase f) ≡ erase (B.if b then t else f)
erase-if B.false t f = refl
erase-if B.true  t f = refl

erase-VERIFYSIG : ∀{Φ}{Γ : Ctx Φ}(mb : Util.Maybe B.Bool)
  → U.VERIFYSIG mb ≡ erase {Φ}{Γ} (A.VERIFYSIG mb)
erase-VERIFYSIG (Util.just B.false) = refl
erase-VERIFYSIG (Util.just B.true)  = refl
erase-VERIFYSIG Util.nothing = refl


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
erase-BUILTIN divideInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN quotientInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN remainderInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _

erase-BUILTIN modInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN lessThanInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i Builtin.Constant.Type.<? j) _ _
erase-BUILTIN lessThanEqualsInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i ≤? j) _ _
erase-BUILTIN greaterThanInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
    erase-decIf (i Builtin.Constant.Type.>? j) _ _
erase-BUILTIN greaterThanEqualsInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i Builtin.Constant.Type.≥? j) _ _
erase-BUILTIN equalsInteger Γ σ _
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i ≟ j) _ _
erase-BUILTIN concatenate Γ σ _
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, tt) = refl
erase-BUILTIN takeByteString Γ σ _
  (A.V-con (integer i) ,, A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN dropByteString Γ σ _
  (A.V-con (integer i) ,, A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN sha2-256 Γ σ _
  (A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN sha3-256 Γ σ _
  (A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN verifySignature Γ σ _
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, A.V-con (bytestring b'') ,, tt) =
  erase-VERIFYSIG _
erase-BUILTIN equalsByteString Γ σ _
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, tt) =
  erase-if (equals b b') _ _     
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
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel p q r) with erase—→ p
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel {t' = t'} p q r) | inj₁ x = inj₁ (subst
    (builtin bn (eraseTel tel) U.—→_)
    (cong (builtin bn) (sym (erase-reconstTel Bs Ds σ telB t' q telD)))
    (U.ξ-builtin
      bn
      (eraseTel tel)
      (eraseVTel _ _ σ _ _ vtel)
      x
      (eraseTel telD)
      (eraseTel telB ++ erase t' ∷ eraseTel telD) refl))
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel {t = t}{t' = t'} p q r) | inj₂ y
  = inj₂ (cong (builtin bn) (trans (trans (cong eraseTel (sym r)) (trans (erase-reconstTel Bs Ds σ telB t q telD) (cong (λ t → eraseTel telB ++ t ∷ eraseTel telD) y))) (sym (erase-reconstTel Bs Ds σ telB t' q telD))))
\end{code}

-- returning nothing means that the typed step vanishes

\begin{code}
eraseProgress : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(M : Γ ⊢ A)(p : A.Progress M)
  → U.Progress (erase M)
  ⊎ Σ (Γ ⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
eraseProgress M (A.step {N = N} p) =
  map U.step (λ q → N ,, p ,, q) (erase—→ p)
eraseProgress M (A.done V)    = inj₁ (U.done (eraseVal V))
eraseProgress M (A.neutral N) = inj₁ (U.neutral (eraseNe N))
eraseProgress M (A.error e)   = inj₁ (U.error (eraseErr e))

erase-progress : ∀{Φ}{Γ : Ctx Φ}{A}(M : Γ ⊢ A)
  → U.Progress (erase M)
  ⊎ Σ (Γ ⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
erase-progress t = eraseProgress t (A.progress t)
\end{code}
