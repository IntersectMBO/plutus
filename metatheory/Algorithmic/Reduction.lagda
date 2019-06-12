\begin{code}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function hiding (_∋_)
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
data Value :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{x : String}{N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ x N)

  V-Λ : ∀ {Φ Γ K}{x : String}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
    → Value N
      ----------------
    → Value (Λ x N)

  V-wrap : ∀{Φ Γ K}
   → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Value term
   → Value (wrap1 pat arg term)

  V-con : ∀{Φ Γ}{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value {Γ = Γ} (con {Φ} cn)
\end{code}

\begin{code}
VTel : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *)) → Tel Γ Δ σ As → Set

data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)

  -- error inside somewhere
  E-Λ : ∀{Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *} {L : Γ ,⋆ K ⊢ B}
    → Error L → Error (Λ x L)
  E-·₁ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error L → Error (L · M)
  E-·₂ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error M → Error (L · M)
  E-·⋆ : ∀{Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}{L : Γ ⊢ Π x B}{A : Φ ⊢Nf⋆ K}
    → Error L → Error (L ·⋆ A)
  E-unwrap : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {L : Γ ⊢ ne (μ1 · pat · arg)}
    → Error L
    → Error (unwrap1 L)
  E-wrap : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → Error term
    → Error (wrap1 pat arg term) 
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
\end{code}

\begin{code}
data Neutral :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  N-` : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *}(x : Γ ∋ A) → Neutral (` x)
  N-· : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}{L : Γ ⊢ A ⇒ B} → Neutral L →
    (M : Γ ⊢ A) → Neutral (L · M)
  N-·⋆ : ∀{Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}{L : Γ ⊢ Π x B} → Neutral L →
    (A : Φ ⊢Nf⋆ K) → Neutral (L ·⋆ A)
  N-unwrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢ ne (μ1 · pat · arg)}
    → Neutral term
    → Neutral (unwrap1 term)
  N-wrap : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → Neutral term
    → Neutral (wrap1 pat arg term)

  N-Λ : ∀ {Φ Γ K x}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → {t : Γ ,⋆ K ⊢ B}
    → Neutral t
    → Neutral (Λ x t)

  N-builtin : ∀{Φ Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → (vtel : VTel Γ Δ σ Bs telB)
    → ∀{C}{t : Γ ⊢ substNf σ C}
    → Neutral t
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (telD : Tel Γ Δ σ Ds)
    → Neutral (builtin bn σ tel)

VERIFYSIG : ∀{Φ}{Γ : Ctx Φ} → Maybe Bool.Bool → Γ ⊢ booleanNf
VERIFYSIG (just Bool.false) = false
VERIFYSIG (just Bool.true)  = true
VERIFYSIG nothing           = error booleanNf

BUILTIN : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As tel)
      -----------------------------
    → Γ ⊢ substNf σ C
BUILTIN addInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = con (integer (i + j))
BUILTIN subtractInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = con (integer (i - j))
BUILTIN multiplyInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) = con (integer (i ** j))
BUILTIN divideInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (div i j)))
BUILTIN quotientInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (quot i j)))
BUILTIN remainderInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (rem i j)))
BUILTIN modInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (mod i j)))
BUILTIN lessThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.<? j) true false
BUILTIN lessThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i ≤? j) true false
BUILTIN greaterThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.>? j) true false
BUILTIN greaterThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.≥? j) true false
BUILTIN equalsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i ≟ j) true false
BUILTIN concatenate _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  con (bytestring (append b b'))
BUILTIN takeByteString _ _ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  con (bytestring (take i b))
BUILTIN dropByteString _ _ (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  con (bytestring (drop i b))
BUILTIN sha2-256 _ _ (V-con (bytestring b) ,, tt) = con (bytestring (SHA2-256 b))
BUILTIN sha3-256 _ _ (V-con (bytestring b) ,, tt) = con (bytestring (SHA3-256 b))
BUILTIN verifySignature _ _ (V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt) = VERIFYSIG (verifySig k d c)
BUILTIN equalsByteString _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  Bool.if (equals b b') then true else false
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

data _—→_ : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{x}{L L' : Γ ,⋆ K ⊢ B}
    → L —→ L'
      ---------------
    → Λ x L —→ Λ x L'

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

  β-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{x}{N : Γ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ x N) ·⋆ A —→ N [ A ]⋆

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

  ξ-wrap : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {M M' : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → M —→ M'
    → wrap1 pat arg M —→ wrap1 pat arg M'

  β-builtin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As tel)
      -----------------------------
    → builtin bn σ tel —→ BUILTIN bn σ tel vtel
    
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
data _—↠_ {Φ Γ} : {A A' : Φ ⊢Nf⋆ *} → Γ ⊢ A → Γ ⊢ A' → Set
  where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : Φ ⊢Nf⋆ *}{M  M' M'' : Γ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
data Progress {Φ}{Γ}{A : Φ ⊢Nf⋆ *} (M : Γ ⊢ A) : Set where
  step : ∀{N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
  neutral :
      Neutral M
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

  neutral : ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → VTel Γ Δ σ Bs telB
    → ∀{C}{t  : Γ ⊢ substNf σ C}
    → Neutral t
    → Bs ++ (C ∷ Ds) ≡ As
    → Tel Γ Δ σ Ds
    → TelProgress tel
\end{code}

\begin{code}
progress-· :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}{t : Γ ⊢ A ⇒ B} → Progress t → (u : Γ ⊢ A)
  → Progress (t · u)
progress-· (step p)         u = step (ξ-·₁ p)
progress-· (done V-ƛ)       u = step β-ƛ
progress-· (neutral p)      u = neutral (N-· p u)
progress-· (error e)        u = error (E-·₁ e)

progress-·⋆ :  ∀{Φ Γ}{K x B}{t : Γ ⊢ Π x B} → Progress t → (A : Φ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)       A = step (ξ-·⋆ p)
progress-·⋆ (done (V-Λ p)) A = step β-Λ
progress-·⋆ (neutral p)    A = neutral (N-·⋆ p A)
progress-·⋆ (error e)      A = error (E-·⋆ e)

progress-unwrap : ∀{Φ Γ K}{pat}{arg : Φ ⊢Nf⋆ K}{t : Γ ⊢ ne ((μ1 · pat) · arg)}
  → Progress t → Progress (unwrap1 t)
progress-unwrap (step p)           = step (ξ-unwrap1 p)
progress-unwrap (done (V-wrap p)) = step β-wrap1
progress-unwrap (neutral p)        = neutral (N-unwrap1 p)
progress-unwrap (error e)          = error (E-unwrap e)

progress-builtin : ∀{Φ Γ} bn
  (σ : ∀{J} → proj₁ (SIG bn) ∋⋆ J → Φ ⊢Nf⋆ J)
  (tel : Tel Γ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn))))
  → TelProgress tel
  → Progress (builtin bn σ tel)
progress-builtin bn σ tel (done vtel)                      =
  step (β-builtin bn σ tel vtel)
progress-builtin bn σ tel (step Bs Ds telB vtel p q telD)  =
  step (ξ-builtin bn σ tel Bs Ds telB telD vtel p q)
progress-builtin bn σ tel (error Bs Ds telB vtel e p telD) =
  error (E-builtin bn σ tel Bs Ds telB vtel e p telD)
progress-builtin bn σ tel (neutral Bs Ds telB vtel e p telD) =
  neutral (N-builtin bn σ tel Bs Ds telB vtel e p telD)

progress : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → (M : Γ ⊢ A) → Progress M

progressTelCons : ∀ {Φ}{Γ : Ctx Φ}{Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {A : Δ ⊢Nf⋆ *}
  → {t : Γ ⊢ substNf σ A}
  → Progress t
  → {As : List (Δ ⊢Nf⋆ *)}
  → {tel : Tel  Γ Δ σ As}
  → TelProgress tel
  → TelProgress {As = A ∷ As} (t ,, tel)
progressTelCons (step p){As}{tel}   q                                =
  step [] As tt tt p refl tel
progressTelCons (done v)            (done vtel)                      =
  done (v ,, vtel)
progressTelCons (done v)            (step Bs Ds telB vtel p q telD)  =
  step (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) p (cong (_ ∷_) q) telD
progressTelCons (done v)            (error Bs Ds telB vtel e p telD) =
  error (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) e (cong (_ ∷_) p) telD
progressTelCons (done v)            (neutral Bs Ds telB vtel e p telD) =
  neutral (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) e (cong (_ ∷_) p) telD
progressTelCons (error e) {As}{tel} q                                =
  error [] As tt tt e refl tel
progressTelCons (neutral p) {As}{tel} q                              =
  neutral [] As tt tt p refl tel

progressTel : ∀ {Φ Γ Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {As : List (Δ ⊢Nf⋆ *)}
  → (tel : Tel Γ Δ σ As)
  → TelProgress tel
progressTel {As = []}     tt         = done tt
progressTel {As = A ∷ As} (t ,, tel) =
  progressTelCons (progress t) (progressTel tel)

progress-Λ : ∀{Φ Γ K x}{B : Φ ,⋆ K ⊢Nf⋆ *}{M : Γ ,⋆ K ⊢ B}
  → Progress M → Progress (Λ x M)
progress-Λ (step p)    = step (ξ-Λ p)
progress-Λ (done p)    = done (V-Λ p)
progress-Λ (neutral p) = neutral (N-Λ p)
progress-Λ (error e)   = error (E-Λ e)

progress-wrap :  ∀{Φ Γ K}
   → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Progress term → Progress (wrap1 pat arg term)
progress-wrap (step p)    = step (ξ-wrap p)
progress-wrap (done v)    = done (V-wrap v)
progress-wrap (neutral p) = neutral (N-wrap p)
progress-wrap (error e)   = error (E-wrap e)

progress (` x)                = neutral (N-` x)
progress (ƛ x M)              = done V-ƛ
progress (M · N)              = progress-· (progress M) N
progress (Λ _ M)              = progress-Λ (progress M)
progress (M ·⋆ A)             = progress-·⋆ (progress M) A
progress (wrap1 pat arg term) = progress-wrap (progress term)
progress (unwrap1 M)          = progress-unwrap (progress M)
progress (con c)              = done (V-con c)
progress (builtin bn σ X)     = progress-builtin bn σ X (progressTel X)
progress (error A)            = error E-error
