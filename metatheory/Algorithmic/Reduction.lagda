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
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_) renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.List hiding ([_]; take; drop)
import Data.Bool as Bool
open import Data.Nat using (zero)

open import Type
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Utils

open import Data.String using (String)
\end{code}

## Values

\begin{code}
data Value :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Φ Γ K}
   → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  _}
   → Value term
   → Value (wrap1 pat arg term)

  V-con : ∀{Φ Γ}{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value {Γ = Γ} (con {Φ} cn)
\end{code}

\begin{code}
VTel : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → Tel Γ Δ σ As → Set

data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)

  -- error inside somewhere
  E-Λ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *} {L : Γ ,⋆ K ⊢ B}
    → Error L → Error (Λ L)
  E-·₁ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error L → Error (L · M)
  E-·₂ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}{M : Γ ⊢ A}
    → Error M → Error (L · M)
  E-·⋆ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}
    {L : Γ ⊢ Π B}{A : Φ ⊢Nf⋆ K}
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
    → {term : Γ ⊢  _}
    → Error term
    → Error (wrap1 pat arg term) 
  E-builtin : ∀{Φ Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (telB : Tel Γ Δ σ Bs)
    → (vtel : VTel Γ Δ σ Bs telB)
    → ∀{D}{t : Γ ⊢ substNf σ D}
    → Error t
    → (p : Bs ++ (D ∷ Ds) ≡ As)
    → (telD : Tel Γ Δ σ Ds)
    → Error (builtin bn σ tel)
\end{code}

\begin{code}
-- this should be a predicate over telescopes

VTel Γ Δ σ []       tt         = ⊤
VTel Γ Δ σ (A ∷ As) (t ,, tel) = Value t × VTel Γ Δ σ As tel

convVal :  ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}(p : Γ ≡ Γ')(q : A ≡ A')
  → ∀{t : Γ ⊢ A} → Value t → Value (conv⊢ p q t)
convVal refl refl v = v
\end{code}

\begin{code}
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
BUILTIN addInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i + j))
BUILTIN subtractInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i - j))
BUILTIN multiplyInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i ** j))
BUILTIN divideInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (div i j)))
BUILTIN quotientInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (quot i j)))
BUILTIN remainderInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (rem i j)))
BUILTIN modInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (mod i j)))
BUILTIN lessThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i <? j) true false
BUILTIN lessThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)
  = decIf (i ≤? j) true false
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
BUILTIN sha2-256 _ _ (V-con (bytestring b) ,, tt) =
  con (bytestring (SHA2-256 b))
BUILTIN sha3-256 _ _ (V-con (bytestring b) ,, tt) =
  con (bytestring (SHA3-256 b))
BUILTIN verifySignature _ _ (V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt) = VERIFYSIG (verifySig k d c)
BUILTIN equalsByteString _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = Bool.if (equals b b') then true else false
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

data _—→_ : ∀ {Φ Γ} {A A' : Φ ⊢Nf⋆ *} → (Γ ⊢ A) → (Γ ⊢ A') → Set where

  ξ-·₁ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{L L' : Γ ⊢ Π B}{A}
    → L —→ L'
      -----------------
    → L ·⋆ A —→ L' ·⋆ A

  β-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{N : Γ , A ⊢ B} {W : Γ ⊢ A}
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A —→ N [ A ]⋆

  β-wrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢ _}
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
    → ∀{D}{t t' : Γ ⊢ substNf σ D}
    → t —→ t'
    → (p : Bs ++ (D ∷ Ds) ≡ As)
    → (q : reconstTel Bs Ds σ telB t p telD ≡ tel)
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
  step : ∀{N : Γ ⊢ A}
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
    → (telD : Tel Γ Δ σ Ds)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (q : reconstTel Bs Ds σ telB t p telD ≡ tel)
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
progress-· :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}{t : Γ ⊢ A ⇒ B} → Progress t → (u : Γ ⊢ A)
  → Progress (t · u)
progress-· (step p)         u = step (ξ-·₁ p)
progress-· (done V-ƛ)       u = step β-ƛ
progress-· (error e)        u = error (E-·₁ e)

progress-·⋆ :  ∀{Φ Γ}{K B}{t : Γ ⊢ Π B} → Progress t → (A : Φ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)   A = step (ξ-·⋆ p)
progress-·⋆ (done V-Λ) A = step β-Λ
progress-·⋆ (error e)  A = error (E-·⋆ e)

progress-unwrap : ∀{Φ Γ K}{pat}{arg : Φ ⊢Nf⋆ K}{t : Γ ⊢ ne ((μ1 · pat) · arg)}
  → Progress t → Progress (unwrap1 t)
progress-unwrap (step q)          = step (ξ-unwrap1 q)
progress-unwrap (done (V-wrap {term = t} v)) = step β-wrap1
progress-unwrap (error e)          = error (E-unwrap e)

progress-builtin : ∀{Φ Γ} bn
  (σ : ∀{J} → proj₁ (SIG bn) ∋⋆ J → Φ ⊢Nf⋆ J)
  (tel : Tel Γ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn))))
  → TelProgress tel
  → Progress (builtin bn σ tel)
progress-builtin bn σ tel (done vtel)                       =
  step (β-builtin bn σ tel vtel)
progress-builtin bn σ tel (step Bs Ds telB vtel p telD q r) =
  step (ξ-builtin bn σ tel Bs Ds telB telD vtel p q r)
progress-builtin bn σ tel (error Bs Ds telB vtel e p telD)  =
  error (E-builtin bn σ tel Bs Ds telB vtel e p telD)

NoVar : ∀{Φ} → Ctx Φ → Set 
NoVar ∅        = ⊤
NoVar (Γ ,⋆ J) = NoVar Γ
NoVar (Γ ,  A) = ⊥

noVar : ∀{Φ}{Γ : Ctx Φ} → NoVar Γ → {A : Φ ⊢Nf⋆ *} → Γ ∋ A → ⊥
noVar p (T x) = noVar p x

progress : ∀{Φ Γ} → NoVar Γ → {A : Φ ⊢Nf⋆ *} → (M : Γ ⊢ A) → Progress M

progressTelCons : ∀ {Φ}{Γ : Ctx Φ} → NoVar Γ → ∀{Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {A : Δ ⊢Nf⋆ *}
  → {t : Γ ⊢ substNf σ A}
  → Progress t
  → {As : List (Δ ⊢Nf⋆ *)}
  → {tel : Tel  Γ Δ σ As}
  → TelProgress tel
  → TelProgress {As = A ∷ As} (t ,, tel)
progressTelCons n (step p){As}{tel}   q                                =
   step [] As tt tt p  tel refl refl 
progressTelCons n (done v)            (done vtel)                      =
  done (v ,, vtel)
progressTelCons n (done v)            (step Bs Ds telB vtel p telD refl r)  =
   step (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) p telD refl (cong (_ ,,_) r) 
progressTelCons n (done v)            (error Bs Ds telB vtel e p telD) =
  error (_ ∷ Bs) Ds (_ ,, telB) (v ,, vtel) e (cong (_ ∷_) p) telD
progressTelCons n (error e) {As}{tel} q                                =
  error [] As tt tt e refl tel

progressTel : ∀ {Φ Γ} → NoVar Γ → ∀{Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {As : List (Δ ⊢Nf⋆ *)}
  → (tel : Tel Γ Δ σ As)
  → TelProgress tel
progressTel p {As = []}     tt         = done tt
progressTel p {As = A ∷ As} (t ,, tel) =
  progressTelCons p (progress p t) (progressTel p tel)

progress-wrap :  ∀{Φ Γ} → NoVar Γ  → ∀{K}
   → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : Φ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Progress term → Progress (wrap1 pat arg term)
progress-wrap n (step p)    = step (ξ-wrap p)
progress-wrap n (done v)    = done (V-wrap v)
progress-wrap n (error e)   = error (E-wrap e)

progress p (` x)                = ⊥-elim (noVar p x)
progress p (ƛ M)                = done V-ƛ
progress p (M · N)              = progress-· (progress p M) N
progress p (Λ M)                = done V-Λ
progress p (M ·⋆ A)             = progress-·⋆ (progress p M) A
progress p (wrap1 pat arg term) = progress-wrap p (progress p term)
progress p (unwrap1 M)          = progress-unwrap (progress p M)
progress p (con c)              = done (V-con c)
progress p (builtin bn σ X)     = progress-builtin bn σ X (progressTel p X)
progress p (error A)            = error E-error
