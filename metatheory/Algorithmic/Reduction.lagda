\begin{code}
module Algorithmic.Reduction where
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
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List hiding ([_]; take; drop)
import Data.Bool as Bool
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_)
open import Type
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Utils
open import Data.String hiding (_++_; _≟_)
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Φ Γ} {A : Φ ⊢Nf⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{x : String}{N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ x N)

  V-Λ_ : ∀ {Φ Γ K}{x : String}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ x N)

  V-wrap1 : ∀{Φ Γ K}
   → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Value (wrap1 pat arg term)

  V-con : ∀{Φ Γ}{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value {Γ = Γ} (con {Φ} cn)

\end{code}

\begin{code}
VTel : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *)) → Tel Γ Δ σ As → Set

data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- a genuine runtime error returned from a builtin
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)

  -- error inside somewhere
  E-·₁ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error L → Error (L · M)
  E-·₂ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error M → Error (L · M)
  E-·⋆ : ∀{Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}{L : Γ ⊢ Π x B}{A : Φ ⊢Nf⋆ K}
    → Error L → Error (L ·⋆ A)
  E-unwrap : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {L : Γ ⊢ ne (μ1 · pat · arg)} → Error L → Error (unwrap1 L)

  E-builtin : ∀{Φ Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → (vtel : VTel Γ Δ σ Bs telB)
    → ∀{C}{t : Γ ⊢ substNf σ C}
    → Error t
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (telD : Tel Γ Δ σ Ds)
    → Error (builtin bn σ tel)
\end{code}

\begin{code}
-- this should be a predicate over telescopes

VTel Γ Δ σ []       tt         = ⊤
VTel Γ Δ σ (A ∷ As) (t ,, tel) = Value t × VTel Γ Δ σ As tel

BUILTIN : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As tel)
      -----------------------------
    → Maybe (Γ ⊢ substNf σ C)
BUILTIN addInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = just (con (integer (i + j)))
BUILTIN subtractInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = just (con (integer (i - j)))
BUILTIN multiplyInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = just (con (integer (i ** j)))
BUILTIN divideInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) with ∣ j ∣ Data.Nat.≟ zero
... | yes p = nothing
... | no ¬p = just (con (integer (div i j)))
BUILTIN quotientInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) with ∣ j ∣ Data.Nat.≟ zero
... | yes p = nothing
... | no ¬p = just (con (integer (quot i j)))
BUILTIN remainderInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) with ∣ j ∣ Data.Nat.≟ zero
... | yes p = nothing
... | no ¬p = just (con (integer (rem i j)))
BUILTIN modInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) with ∣ j ∣ Data.Nat.≟ zero
... | yes p = nothing
... | no ¬p = just (con (integer (mod i j)))
BUILTIN lessThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)  with i Builtin.Constant.Type.<? j
... | yes _ = just true
... | no _  = just false
BUILTIN lessThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) with i ≤? j
... | yes _ = just true
... | no _  = just false
BUILTIN greaterThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)
  with i Builtin.Constant.Type.>? j
... | yes _ = just true
... | no _  = just false
BUILTIN greaterThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)
  with i Builtin.Constant.Type.≥? j
... | yes _ = just true
... | no _  = just false
BUILTIN equalsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)
  with i ≟ j
... | yes _ = just true
... | no _  = just false
BUILTIN concatenate _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  just (con (bytestring (append b b')))
BUILTIN takeByteString _ _ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  just (con (bytestring (take i b)))
BUILTIN dropByteString _ _ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  just (con (bytestring (drop i b)))
BUILTIN sha2-256 _ _ (V-con (bytestring b) ,, tt) = just (con (bytestring (SHA2-256 b)))
BUILTIN sha3-256 _ _ (V-con (bytestring b) ,, tt) = just (con (bytestring (SHA3-256 b)))
BUILTIN verifySignature _ _ (V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt)
  with verifySig k d c
... | just Bool.true  = just true
... | just Bool.false = just false
... | nothing = nothing
BUILTIN equalsByteString _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt)
  with equals b b'
... | Bool.true  = just true
... | Bool.false = just false
\end{code}


# recontructing the telescope after a reduction step

\begin{code}
reconstTel : ∀{Φ Γ Δ As} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : Tel Γ Δ σ Bs)
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → Tel Γ Δ σ As
reconstTel [] Ds σ telB t' refl telD = t' ,, telD
reconstTel (B ∷ Bs) Ds σ (X ,, telB) t' refl tel' =
  X ,, reconstTel Bs Ds σ telB t' refl tel'
\end{code}


## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Φ Γ} {A : Φ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}{L L′ : Γ ⊢ Π x B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

  β-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{x}{N : Γ , A ⊢ B} {W : Γ ⊢ A}
--    → Value W
      -------------------
    → (ƛ x N) · W —→ N [ W ]

  β-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{x}{N : Γ ,⋆ K ⊢ B}{W}
      -------------------
    → (Λ x N) ·⋆ W —→ N [ W ]⋆

  β-wrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {M M' : Γ ⊢ ne (μ1 · pat · arg)}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'

  β-builtin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As tel)
      -----------------------------
    → builtin bn σ tel —→ maybe id (error _) (BUILTIN bn σ tel vtel)
    
  ξ-builtin : ∀{Φ Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → (telD : Tel Γ Δ σ Ds)
    → (vtel : VTel Γ Δ σ Bs telB)
    → ∀{C}{t t' : Γ ⊢ substNf σ C}
    → t —→ t'
    → (p : Bs ++ (C ∷ Ds) ≡ As)
--    → (q : telB ++ (t ∷ telD) ≡ tel) -- need to define ++ for tels
    → builtin bn σ tel —→ builtin bn σ (reconstTel Bs Ds σ telB t' p telD)
\end{code}

\begin{code}
data _—↠_ {J Φ Γ} : {A : Φ ⊢Nf⋆ J}{A' : Φ ⊢Nf⋆ J} → Γ ⊢ A → Γ ⊢ A' → Set
  where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : Φ ⊢Nf⋆ J}{M  M' M'' : Γ ⊢ A}
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
  error :
      Error M
      -------
    → Progress M
\end{code}

\begin{code}

data TelProgress
  {Φ Γ}
  {Δ}
  {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  {As : List (Δ ⊢Nf⋆ *)}
  (tel : Tel Γ Δ σ As)
  : Set where
  done : VTel Γ Δ σ As tel → TelProgress tel
  step : ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → VTel Γ Δ σ Bs telB
    → ∀{C}{t t' : Γ ⊢ substNf σ C}
    → t —→ t'
    → Bs ++ (C ∷ Ds) ≡ As
    → Tel Γ Δ σ Ds
    → TelProgress tel
  error : ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → VTel Γ Δ σ Bs telB
    → ∀{C}{t  : Γ ⊢ substNf σ C}
    → Error t
    → Bs ++ (C ∷ Ds) ≡ As
    → Tel Γ Δ σ Ds
    → TelProgress tel

\end{code}

\begin{code}
progress· : ∀{A B}{t : ∅ ⊢ A ⇒ B} → Progress t → (u : ∅ ⊢ A)
  → Progress (t · u)
progress· (step p)  u = step (ξ-·₁ p)
progress· (done V-ƛ) u = step β-ƛ
progress· (error e) u = error (E-·₁ e)

progress·⋆ : ∀{K x B}{t : ∅ ⊢ Π x B} → Progress t → (A : ∅ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress·⋆ (step p)  A = step (ξ-·⋆ p)
progress·⋆ (done V-Λ_) A = step β-Λ
progress·⋆ (error e) A = error (E-·⋆ e)

progress-unwrap : ∀{K}{pat}{arg : ∅ ⊢Nf⋆ K}{t : ∅ ⊢ ne ((μ1 · pat) · arg)}
  → Progress t → Progress (unwrap1 t)
progress-unwrap (step p) = step (ξ-unwrap1 p)
progress-unwrap (done V-wrap1) = step β-wrap1
progress-unwrap (error e) = error (E-unwrap e)

progress-builtin : ∀ bn (σ : ∀{J} → proj₁ (SIG bn) ∋⋆ J → ∅ ⊢Nf⋆ J)(tel : Tel ∅ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn)))) → TelProgress tel → Progress (builtin bn σ tel)
progress-builtin bn σ tel (done vtel)                      = step (β-builtin bn σ tel vtel)
progress-builtin bn σ tel (step Bs Ds telB vtel p q telD)  = step (ξ-builtin bn σ tel Bs Ds telB telD vtel p q)
progress-builtin bn σ tel (error Bs Ds telB vtel e p telD) = error (E-builtin bn σ tel Bs Ds telB vtel e p telD)

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M

progressTelCons : ∀ {Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}
  → {A : Δ ⊢Nf⋆ *}
  → {t : ∅ ⊢ substNf σ A}
  → Progress t
  → {As : List (Δ ⊢Nf⋆ *)}
  → {tel : Tel ∅ Δ σ As}
  → TelProgress tel
  → TelProgress {As = A ∷ As} (t ,, tel)
progressTelCons (step p){As}{tel}   q                                = step [] As tt tt p refl tel
progressTelCons (done v)            (done vtel)                      = done (v ,, vtel)
progressTelCons (done v)            (step Bs Ds telB vtel p q telD)  = step (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) p (cong (_ ∷_) q) telD
progressTelCons (done v)            (error Bs Ds telB vtel e p telD) = error (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) e (cong (_ ∷_) p) telD
progressTelCons (error e) {As}{tel} q                                = error [] As tt tt e refl tel

progressTel : ∀ {Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → ∅ ⊢Nf⋆ K}
  → {As : List (Δ ⊢Nf⋆ *)}
  → (tel : Tel ∅ Δ σ As)
  → TelProgress tel
progressTel {As = []}     tt         = done tt
progressTel {As = A ∷ As} (t ,, tel) = progressTelCons (progress t) (progressTel tel)

progress (` ())
progress (ƛ x M)              = done V-ƛ
progress (M · N)              = progress· (progress M) N
progress (Λ _ M)              = done V-Λ_
progress (M ·⋆ A)             = progress·⋆ (progress M) A
progress (wrap1 pat arg term) = done V-wrap1
progress (unwrap1 M)          = progress-unwrap (progress M)
progress (con c)              = done (V-con c)
progress (builtin bn σ X)     = progress-builtin bn σ X (progressTel X)
progress (error A)            = error E-error
