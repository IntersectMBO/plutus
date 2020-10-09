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
  ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Type.BetaNBE.RenamingSubstitution
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List using (List;[];_∷_)
open import Data.Vec hiding (map; [_])
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
import Utils as Util
open import Relation.Nullary
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_; _*_)
open import Data.Integer hiding (suc)
open import Data.Fin using (suc)
import Data.Bool as B
\end{code}

\begin{code}
eraseVal : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : A.Ctx Φ}{t : Γ A.⊢ A}
  → A.Value t → U.Value (erase t)
eraseVal (A.V-ƛ t)      = U.V-F (U.V-ƛ (erase t))
eraseVal (A.V-Λ t)      = U.V-F (U.V-ƛ (U.weaken (erase t)))
eraseVal (A.V-wrap v)         = eraseVal v
eraseVal (A.V-con {Γ = Γ} cn) = U.V-con (eraseTC {Γ = Γ} cn)

eraseFVal : ∀{Φ}{A B : Φ ⊢Nf⋆ *}{Γ : A.Ctx Φ}{t : Γ A.⊢ A ⇒ B}
  → A.Value t → U.FValue (erase t)
eraseFVal (A.V-ƛ t) = U.V-ƛ (erase t)

eraseErr : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : A.Ctx Φ}{e : Γ A.⊢ A}
  → A.Error e → U.Error (erase e)
eraseErr A.E-error = U.E-error

eraseVTel : ∀ {Φ} Γ Δ
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (As : List (Δ ⊢Nf⋆ *))
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.VTel (Data.List.length As) (len Γ) (eraseTel tel)
eraseVTel Γ Δ σ []       tel       vtel        = _ 
eraseVTel Γ Δ σ (A ∷ As) (t A.∷ tel) (v ,, vtel) =
  eraseVal v ,, eraseVTel Γ Δ σ As tel vtel 

eraseVTel⋆ : ∀ {Φ}(Γ : A.Ctx Φ) Δ
  → U.VTel (len⋆ Δ) (len Γ) (eraseTel⋆ Γ Δ)
eraseVTel⋆ Γ ∅        = tt
eraseVTel⋆ Γ (Δ ,⋆ K) =
  U.vTel:< (eraseTel⋆ Γ Δ) (eraseVTel⋆ Γ Δ) (con unit) (U.V-con unit)

eraseVTel' : ∀ {Φ} Γ Δ
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (As : List (Δ ⊢Nf⋆ *))
  → ∀{n}(p : len⋆ Δ Data.Nat.+ Data.List.length As ≡ n)
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.VTel n (len Γ) (subst (λ n → Untyped.Tel n (len Γ)) p (eraseTel⋆ Γ Δ ++ eraseTel tel))
eraseVTel' Γ Δ σ As refl ts vs = U.vTel++ (eraseTel⋆ Γ Δ) (eraseVTel⋆ Γ Δ) (eraseTel ts) (eraseVTel Γ Δ σ As ts vs)

eraseAnyErr : ∀{Φ}{Γ}{Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As}(ts : A.Tel Γ Δ σ As) → A.Any A.Error ts → U.Any U.Error (eraseTel ts)
eraseAnyErr .(_ A.∷ _) (A.here p)    = U.here (eraseErr p)
eraseAnyErr .(_ A.∷ _) (A.there v p) = U.there (eraseVal v) (eraseAnyErr _ p)

eraseAnyErr' : ∀{Φ}{Γ}{Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As}
  → ∀{n}(p : len⋆ Δ Data.Nat.+ Data.List.length As ≡ n)
  → (ts : A.Tel Γ Δ σ As)
  → A.Any A.Error ts
  → U.Any U.Error (subst (λ n → Untyped.Tel n (len Γ)) p (eraseTel⋆ Γ Δ ++ eraseTel ts))
eraseAnyErr' {Γ = Γ}{Δ = Δ} refl ts p =
  U.anyErr++ (eraseAnyErr ts p) (eraseTel⋆ Γ Δ) (eraseVTel⋆ Γ Δ)
\end{code}

\begin{code}
erase-decIf : ∀{Φ}{Γ : A.Ctx Φ}{A : Φ ⊢Nf⋆ *}{X}(p : Dec X)(t f : Γ A.⊢ A) →
  Util.decIf p (erase t) (erase f) ≡ erase (Util.decIf p t f)
erase-decIf (yes p) t f = refl
erase-decIf (no ¬p) t f = refl
{-
erase-if : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢Nf⋆ *}(b : B.Bool)(t f : Γ ⊢ A) →
  (B.if b then erase t else erase f) ≡ erase (B.if b then t else f)
erase-if B.false t f = refl
erase-if B.true  t f = refl
-}
erase-VERIFYSIG : ∀{Φ}{Γ : A.Ctx Φ}(mb : Util.Maybe B.Bool)
  → U.VERIFYSIG mb ≡ erase {Φ}{Γ} (A.VERIFYSIG mb)
erase-VERIFYSIG (Util.just B.false) = refl
erase-VERIFYSIG (Util.just B.true)  = refl
erase-VERIFYSIG Util.nothing = refl

erase-BUILTIN : ∀ bn → let Δ ,, As ,, X = SIG bn in
  ∀{Φ}(Γ : A.Ctx Φ)
  → (σ : ∀{K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.BUILTIN bn (subst (λ n → Untyped.Tel n (len Γ)) (lemma bn) (eraseTel⋆ Γ (proj₁ (SIG bn)) ++ eraseTel tel)) (eraseVTel' Γ Δ σ As (lemma bn) tel vtel)
    ≡ erase (A.BUILTIN bn σ tel vtel)
erase-BUILTIN addInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN subtractInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN multiplyInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) = refl
erase-BUILTIN divideInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN quotientInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN remainderInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN modInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (∣ j ∣ Data.Nat.≟ zero) _ _
erase-BUILTIN lessThanInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i Data.Integer.<? j) _ _
erase-BUILTIN lessThanEqualsInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i ≤? j) _ _
erase-BUILTIN greaterThanInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
    erase-decIf (i Builtin.Constant.Type.>? j) _ _
erase-BUILTIN greaterThanEqualsInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i Builtin.Constant.Type.≥? j) _ _
erase-BUILTIN equalsInteger Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (integer j) ,, tt) =
  erase-decIf (i ≟ j) _ _
erase-BUILTIN concatenate Γ σ (_ ∷ _ ∷ [])
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, tt) = refl
erase-BUILTIN takeByteString Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN dropByteString Γ σ (_ ∷ _ ∷ [])
  (A.V-con (integer i) ,, A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN sha2-256 Γ σ (_ ∷ [])
  (A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN sha3-256 Γ σ (_ ∷ [])
  (A.V-con (bytestring b) ,, tt) = refl
erase-BUILTIN verifySignature Γ σ (_ ∷ _ ∷ _ ∷ [])
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, A.V-con (bytestring b'') ,, tt) =
  erase-VERIFYSIG _
erase-BUILTIN equalsByteString Γ σ (_ ∷ _ ∷ [])
  (A.V-con (bytestring b) ,, A.V-con (bytestring b') ,, tt) = refl
erase-BUILTIN ifThenElse Γ σ (_ ∷ _ ∷ _ ∷ []) (A.V-con (bool B.false) ,, vt ,, vu) = refl
erase-BUILTIN ifThenElse Γ σ (_ ∷ _ ∷ _ ∷ []) (A.V-con (bool B.true)  ,, vt ,, vu) = refl
\end{code}

\begin{code}
subst—→T : ∀{m m' n}{ts ts' : Untyped.Tel m n}
  → ts U.—→T ts'
  → (p : m ≡ m')
  → subst (λ m → Untyped.Tel m n) p ts U.—→T subst (λ m → Untyped.Tel m n) p ts'
subst—→T p refl = p

erase—→ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : A.Ctx Φ}{t t' : Γ A.⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'

erase—→T : ∀{Φ}{Γ : A.Ctx Φ}{Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J}{As : List (Δ ⊢Nf⋆ *)}{ts ts' : A.Tel Γ Δ σ As}
  → ts A.—→T ts'
  → eraseTel ts U.—→T eraseTel ts' ⊎ eraseTel ts ≡ eraseTel ts' 
erase—→T (A.here p)    = map U.here (cong (_∷ _)) (erase—→ p)
erase—→T (A.there v p) = map (U.there (eraseVal v)) (cong (_ ∷_)) (erase—→T p)

erase—→ (A.ξ-·₁ {M = M} p)                              = map
  U.ξ-·₁
  (cong (_· erase M))
  (erase—→ p)
erase—→ (A.ξ-·₂ {V = V} p q)                            = map
  (U.ξ-·₂ (eraseFVal p))
  ((cong (erase V ·_)))
  (erase—→ q)
erase—→ (A.ξ-·⋆ p)                                      =
  map U.ξ-·₁ (cong (_· plc_dummy)) (erase—→ p)
erase—→ (A.β-ƛ {N = N}{V = V} v)                   =
  inj₁ (subst ((ƛ (erase N) · erase V) U.—→_) (lem[] N V) (U.β-ƛ (eraseVal v)))
erase—→ {Γ = Γ} (A.β-Λ {N = N}{A = A})                          =
  inj₁ (subst (ƛ (U.weaken (erase N)) · plc_dummy U.—→_)
              (trans (trans (sym (U.sub-ren
                                   suc
                                   (U.extend ` plc_dummy)
                                   (erase N)))
                            (sym (U.sub-id  (erase N))))
                     (lem[]⋆ N A))
              (U.β-ƛ (eraseVal (A.voidVal Γ))))
erase—→ (A.β-wrap p)                                    = inj₂ refl
erase—→ (A.ξ-unwrap p)                                  = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ {Γ = Γ} (A.β-builtin b σ ts vs)                 = inj₁ (subst
  (Untyped.builtin b (lemma≤ b) (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts) U.—→_)
  (erase-BUILTIN b _ σ ts vs)
  (subst
    (U._—→  U.BUILTIN b (subst (λ n → Untyped.Tel n (len Γ)) (lemma b) (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts)) (eraseVTel' Γ (proj₁ (SIG b)) σ (proj₁ (proj₂ (SIG b))) (lemma b) ts vs))
    (sym (lem-builtin b (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts) (lemma≤ b) ≤‴-refl (lemma b)))
    (U.β-builtin (subst (λ n → Untyped.Tel n (len Γ)) (lemma b) (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts)) (eraseVTel' Γ (proj₁ (SIG b)) σ (proj₁ (proj₂ (SIG b))) (lemma b) ts vs))))
erase—→  {Γ = Γ} (A.ξ-builtin b σ {ts = ts}{ts' = ts'} p) = map
  (λ q → subst₂ U._—→_
    (sym (lem-builtin b (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts) (lemma≤ b) ≤‴-refl (lemma b)))
    (sym (lem-builtin b (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts') (lemma≤ b) ≤‴-refl (lemma b)))
    (U.ξ-builtin b (subst—→T (U.—→T++ q (eraseTel⋆ Γ (proj₁ (SIG b))) (eraseVTel⋆ Γ (proj₁ (SIG b)))) (lemma b))))
  (cong (λ ts → builtin b (lemma≤ b) (eraseTel⋆ Γ (proj₁ (SIG b)) ++ ts)))
  (erase—→T p)
erase—→ (A.E-·₂ p)                                      =
  inj₁ (U.E-·₂ (eraseFVal p))
erase—→ A.E-·₁                                          = inj₁ U.E-·₁
erase—→ A.E-·⋆                                          = inj₁ U.E-·₁
erase—→ A.E-unwrap                                      = inj₂ refl
erase—→ A.E-wrap                                        = inj₂ refl
erase—→ {Γ = Γ} (A.E-builtin b σ ts p) = inj₁ (subst (U._—→ error) (sym (lem-builtin b (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts) (lemma≤ b) ≤‴-refl (lemma b))) (U.E-builtin b (subst (λ n → Untyped.Tel n (len Γ)) (lemma b) (eraseTel⋆ Γ (proj₁ (SIG b)) ++ eraseTel ts)) (eraseAnyErr' (lemma b) ts p)))
\end{code}

-- returning nothing means that the typed step vanishes

\begin{code}
eraseProgress : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(M : Γ A.⊢ A)(p : A.Progress M)
  → U.Progress (erase M)
  ⊎ Σ (Γ A.⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
eraseProgress M (A.step {N = N} p) =
  map U.step (λ q → N ,, p ,, q) (erase—→ p)
eraseProgress M (A.done V)    = inj₁ (U.done (eraseVal V))
eraseProgress M (A.error e)   = inj₁ (U.error (eraseErr e))

erase-progress : ∀{Φ}{Γ : A.Ctx Φ} → A.NoVar Γ → ∀{A}(M : Γ A.⊢ A)
  → U.Progress (erase M)
  ⊎ Σ (Γ A.⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
erase-progress p t = eraseProgress t (A.progress p t)
\end{code}
