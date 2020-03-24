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
open import Data.Bool using (Bool;true;false)
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
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Utils
open import Data.Maybe using (just;from-just)
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
VERIFYSIG : ∀{Φ}{Γ : Ctx Φ} → Maybe Bool → Γ ⊢ con bool
VERIFYSIG (just false) = con (bool false)
VERIFYSIG (just true)  = con (bool true)
VERIFYSIG nothing      = error (con bool)

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
  decIf (i <? j) (con (bool true)) (con (bool false))
BUILTIN lessThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt)
  = decIf (i ≤? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.>? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanEqualsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.≥? j) (con (bool true)) (con (bool false))
BUILTIN equalsInteger _ _ (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i ≟ j) (con (bool true)) (con (bool false))
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
BUILTIN equalsByteString _ _ (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = con (bool (equals b b'))
BUILTIN ifThenElse _ (_ ,, t ,, _ ,, _) (V-con (bool true)  ,, _) = t
BUILTIN ifThenElse _ (_ ,, _ ,, u ,, _) (V-con (bool false) ,, _) = u
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

  β-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}{N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→ N [ V ]

  β-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A —→ N [ A ]⋆

  β-wrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → {term : Γ ⊢ _}
    → Value term
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
    
  ξ-builtin : ∀{Φ Γ} → (bn : Builtin)
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
progress-·V :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → {t : Γ ⊢ A ⇒ B} → Value t
  → {u : Γ ⊢ A} → Progress u
  → Progress (t · u)
progress-·V v   (step q)  = step (ξ-·₂ v q)
progress-·V V-ƛ (done w)  = step (β-ƛ w)
progress-·V v   (error e) = error (E-·₂ e)

progress-· :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → {t : Γ ⊢ A ⇒ B} → Progress t
  → {u : Γ ⊢ A} → Progress u
  → Progress (t · u)
progress-· (step p)   q = step (ξ-·₁ p)
progress-· (done V-ƛ) q = progress-·V V-ƛ q
progress-· (error e)  q = error (E-·₁ e)

progress-·⋆ :  ∀{Φ Γ}{K B}{t : Γ ⊢ Π B} → Progress t → (A : Φ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)   A = step (ξ-·⋆ p)
progress-·⋆ (done V-Λ) A = step β-Λ
progress-·⋆ (error e)  A = error (E-·⋆ e)

progress-unwrap : ∀{Φ Γ K}{pat}{arg : Φ ⊢Nf⋆ K}{t : Γ ⊢ ne ((μ1 · pat) · arg)}
  → Progress t → Progress (unwrap1 t)
progress-unwrap (step q)          = step (ξ-unwrap1 q)
progress-unwrap (done (V-wrap {term = t} v)) = step (β-wrap1 v)
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
progress p (M · N)              = progress-· (progress p M) (progress p N)
progress p (Λ M)                = done V-Λ
progress p (M ·⋆ A)             = progress-·⋆ (progress p M) A
progress p (wrap1 pat arg term) = progress-wrap p (progress p term)
progress p (unwrap1 M)          = progress-unwrap (progress p M)
progress p (con c)              = done (V-con c)
progress p (builtin bn σ X)     = progress-builtin bn σ X (progressTel p X)
progress p (error A)            = error E-error
--

open import Data.Empty

-- progress is disjoint:


-- a value cannot make progress
val : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢ σ} → Value t → ¬ (Σ (Γ ⊢ σ) (t —→_))
val V-ƛ ()
val V-Λ ()
val (V-wrap p) (.(wrap1 _ _ _) ,, ξ-wrap q) = val p (_ ,, q)
val (V-con cn) ()

-- if a term can make progress it cannot be a value
red : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢ σ} → Σ (Γ ⊢ σ) (t —→_) → ¬ (Value t)
red (.(wrap1 _ _ _) ,, ξ-wrap p) (V-wrap v) = red (_ ,, p) v

-- nothing in a telescope of values can make progress
vTel : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → (tel : Tel Γ Δ σ As)
  → (vtel : VTel Γ Δ σ As tel)
  → ∀ Bs Ds
  → (telB : Tel Γ Δ σ Bs)
  → (telD : Tel Γ Δ σ Ds)
  → ∀{D}{t t' : Γ ⊢ substNf σ D}
  → t —→ t'
  → (p : Bs ++ (D ∷ Ds) ≡ As)
  → (q : reconstTel Bs Ds σ telB t p telD ≡ tel)
  → ⊥
vTel Γ Δ σ _ (t ,, tel) (v ,, vtel) [] As telB telD r refl refl =
  val v (_ ,, r)
vTel Γ Δ σ _ (_ ,, tel) (_ ,, vtel) (_ ∷ Bs) Ds (_ ,, telB) telD r refl refl =
  vTel Γ Δ σ _ tel vtel Bs Ds telB telD r refl refl

-- values are unique for a term
valUniq : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}(t : Γ ⊢ A)
  → (v v' : Value t)
  → v ≡ v'
valUniq .(ƛ _) V-ƛ V-ƛ = refl
valUniq .(Λ _) V-Λ V-Λ = refl
valUniq .(wrap1 _ _ _) (V-wrap v) (V-wrap v') = cong V-wrap (valUniq _ v v')
valUniq .(con cn) (V-con cn) (V-con .cn) = refl

-- telescopes of values are unique for that telescope
vTelUniq : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → (tel : Tel Γ Δ σ As)
  → (vtel vtel' : VTel Γ Δ σ As tel)
  → vtel ≡ vtel'
vTelUniq Γ Δ σ [] tel vtel vtel' = refl
vTelUniq Γ Δ σ (A ∷ As) (t ,, tel) (v ,, vtel) (v' ,, vtel') =
  cong₂ _,,_ (valUniq t v v') (vTelUniq Γ Δ σ As tel vtel vtel') 

cong-just : {A : Set}{a a' : A} → Data.Maybe.just a ≡ just a' → a ≡ a'
cong-just refl = refl

-- the ugly stuff concerning `reconstTel` is going to change soon

reconstTel-step : ∀{Φ Γ Δ As C} B Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : Tel Γ Δ σ Bs)
    → (t : Γ ⊢ substNf σ B)
    → (t' : Γ ⊢ substNf σ C)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (p' : B ∷ Bs ++ (C ∷ Ds) ≡ B ∷ As)
    → (tel : Tel Γ Δ σ Ds)
    → reconstTel (B ∷ Bs) Ds σ (t ,, telB) t' p' tel
      ≡
      (t ,, reconstTel Bs Ds σ telB t' p tel)
reconstTel-step B Bs Ds σ telB t t' refl refl tel = refl

reconstTel-irr : ∀{Φ Γ Δ As C} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (telB : Tel Γ Δ σ Bs)
    → (t : Γ ⊢ substNf σ C)
    → (p p' : Bs ++ (C ∷ Ds) ≡ As)
    → (tel : Tel Γ Δ σ Ds)
    → reconstTel Bs Ds σ telB t p tel
      ≡
      reconstTel Bs Ds σ telB t p' tel
reconstTel-irr Bs Ds σ telB t refl refl tel = refl

lemX : ∀{Φ Γ Δ} B Bs Bs'
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (telB : Tel Γ Δ σ Bs)
  → (X : Bs ≡ Bs')
  → (X' : B ∷ Bs ≡ B ∷ Bs')
  → (t : Γ ⊢ substNf σ B)
  → Relation.Binary.PropositionalEquality.subst (Tel Γ Δ σ) (cong (B ∷_) X) (t ,, telB)
    ≡
    (t ,, Relation.Binary.PropositionalEquality.subst (Tel Γ Δ σ) X telB)
lemX B Bs Bs' σ telB refl refl t = refl

reconstTel-inj : ∀{Φ Γ Δ As} Bs Bs' Ds Ds'
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (telB : Tel Γ Δ σ Bs)
  → VTel Γ Δ σ Bs telB
  → (telB' : Tel Γ Δ σ Bs')
  → VTel Γ Δ σ Bs' telB'
  → ∀{C}{t t' : Γ ⊢ substNf σ C}
  → t —→ t'
  → ∀{C'}{t'' t''' : Γ ⊢ substNf σ C'}
  → t'' —→ t'''
  → (p : Bs ++ (C ∷ Ds) ≡ As)
  → (p' : Bs' ++ (C' ∷ Ds') ≡ As)
  → (tel : Tel Γ Δ σ Ds)
  → (tel' : Tel Γ Δ σ Ds')
  → reconstTel Bs Ds σ telB t p tel ≡ reconstTel Bs' Ds' σ telB' t'' p' tel'
  → (Σ (Bs ≡ Bs') λ p → Relation.Binary.PropositionalEquality.subst (Tel Γ Δ σ) p telB ≡ telB')
  × (Σ (C ≡ C') λ p → Relation.Binary.PropositionalEquality.subst (λ C → Γ ⊢ substNf σ C) p t ≡ t'')
  × (Σ (Ds ≡ Ds') λ p → Relation.Binary.PropositionalEquality.subst (Tel Γ Δ σ) p tel ≡ tel')
reconstTel-inj [] [] Ds .Ds σ telB x telB' x₁ x₂ x₃ refl refl tel tel' x₄ = (refl ,, refl) ,, ((refl ,, (cong proj₁ x₄)) ,, (refl ,, (cong proj₂ x₄)))
reconstTel-inj [] (x₅ ∷ Bs') Ds Ds' σ tt tt (t' ,, telB') (v' ,, vtel') q q' refl refl tel tel' x₄ =
  ⊥-elim (val v' (_ ,, Relation.Binary.PropositionalEquality.subst (_—→ _) (cong proj₁ x₄) q))
reconstTel-inj (x₅ ∷ Bs) [] Ds Ds' σ (t ,, telB) (v ,,  vtel) tt tt q q' refl refl tel tel' x₄ =
  ⊥-elim (val v (_ ,, Relation.Binary.PropositionalEquality.subst (_—→ _) (sym (cong proj₁ x₄)) q'))
reconstTel-inj (B ∷ Bs) (B' ∷ Bs') Ds Ds' σ (t ,, telB) (v ,, vtel) (t' ,, telB') (v' ,, vtel') q q' refl p' tel tel' x₄ with cong-just (cong head p')
... | refl with reconstTel-inj Bs Bs' Ds Ds' σ telB vtel telB' vtel' q q' refl (cong-just (cong tail p')) tel tel' (cong proj₂ (trans x₄ (reconstTel-step B' Bs' Ds' σ telB' t' _ (cong-just (cong tail p')) p' tel')))
... | (X ,, X') ,, Y = ((cong (B ∷_) X) ,, (trans (lemX B Bs Bs' σ telB X (cong (B ∷_) X) t) (cong₂ _,,_ (cong proj₁ (trans x₄ (reconstTel-step B' Bs' Ds' σ telB' t' _ (cong-just (cong tail p')) p' tel'))) X'))) ,, Y

det : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t t' t'' : Γ ⊢ σ}
  → (p : t —→ t')(q : t —→ t'') → t' ≡ t''

reconstTel-inj' : ∀{Φ Γ Δ As} Bs Bs' Ds Ds'
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (telB : Tel Γ Δ σ Bs)
  → VTel Γ Δ σ Bs telB
  → (telB' : Tel Γ Δ σ Bs')
  → VTel Γ Δ σ Bs' telB'
  → ∀{C}{t t' : Γ ⊢ substNf σ C}
  → t —→ t'
  → ∀{C'}{t'' t''' : Γ ⊢ substNf σ C'}
  → t'' —→ t'''
  → (p : Bs ++ (C ∷ Ds) ≡ As)
  → (p' : Bs' ++ (C' ∷ Ds') ≡ As)
  → (tel : Tel Γ Δ σ Ds)
  → (tel' : Tel Γ Δ σ Ds')
  → reconstTel Bs Ds σ telB t p tel ≡ reconstTel Bs' Ds' σ telB' t'' p' tel'
  → reconstTel Bs Ds σ telB t' p tel ≡ reconstTel Bs' Ds' σ telB' t''' p' tel'
reconstTel-inj' Bs Bs' Ds Ds' σ telB x telB' x₁ x₂ x₃ p p' tel tel' x₄ with reconstTel-inj Bs Bs' Ds Ds' σ telB x telB' x₁ x₂ x₃ p p' tel tel' x₄
... | (refl ,, refl) ,, (refl ,, refl) ,, (refl ,, refl) with p | p' | det x₂ x₃
... | refl | refl | refl = refl

-- the reduction rules are deterministic

det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ w q) = ⊥-elim (val w (_ ,, p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (val v (_ ,, q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (val w (_ ,, p))
det (ξ-·⋆ p) (ξ-·⋆ q) = cong (_·⋆ _) (det p q)
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (val v (_ ,, q))
det (β-ƛ v) (β-ƛ w) = refl
det β-Λ β-Λ = refl
det (β-wrap1 p) (β-wrap1 q) = refl
det (β-wrap1 p) (ξ-unwrap1 q) = ⊥-elim (val (V-wrap p) (_ ,, q))
det (ξ-unwrap1 p) (β-wrap1 q) = ⊥-elim (val (V-wrap q) (_ ,, p))
det (ξ-unwrap1 p) (ξ-unwrap1 q) = cong unwrap1 (det p q)
det (ξ-wrap p) (ξ-wrap q) = cong (wrap1 _ _) (det p q)
det (β-builtin bn σ tel vtel) (β-builtin .bn .σ .tel wtel) =
   cong (BUILTIN bn σ tel) (vTelUniq _ _ σ _ tel vtel wtel)
det (β-builtin bn σ tel vtel) (ξ-builtin .bn .σ .tel Bs Ds telB telD wtel q p q₁) = ⊥-elim (vTel _ _ σ _ tel vtel Bs  Ds telB telD q p q₁)
det (ξ-builtin bn σ tel Bs Ds telB telD vtel p p₁ q) (β-builtin .bn .σ .tel vtel₁) = ⊥-elim (vTel _ _ σ _ tel vtel₁ Bs Ds telB telD p p₁ q)
det (ξ-builtin bn σ tel Bs Ds telB telD vtel p p₁ q) (ξ-builtin .bn .σ .tel Bs' Ds' telB' telD' vtel' p' p'' q') = cong (builtin bn σ) (reconstTel-inj' Bs Bs' Ds Ds' σ telB vtel telB' vtel' p p' p₁ p'' telD telD' (trans q (sym q')))
