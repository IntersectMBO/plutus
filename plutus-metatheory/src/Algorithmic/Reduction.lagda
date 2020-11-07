\begin{code}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
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
open import Data.Unit using (tt)


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

  V-ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → (M : Γ , A ⊢ B)
      ---------------------------
    → Value (ƛ M)

  V-Λ : ∀ {Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}
    → (M : Γ ,⋆ K ⊢ B)
      ----------------
    → Value (Λ M)

  V-wrap : ∀{Φ Γ K}
   → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : Φ ⊢Nf⋆ K}
   → {M : Γ ⊢  _}
   → Value M
   → Value (wrap A B M)

  V-con : ∀{Φ Γ}{tcn : TyCon}
    → (cn : TermCon (con tcn))
    → Value {Γ = Γ} (con {Φ} cn)

  V-builtin : ∀{Φ Γ}(b : Builtin)
    → let Ψ ,, As ,, C = SIG b in
      (σ : SubNf Ψ Φ)
    → (A : Ψ ⊢Nf⋆ *)
    → (As' : List (Ψ ⊢Nf⋆ *))
    → (p : (A ∷ As') ≤L' As)
    → (ts : Tel Γ Ψ σ As')
    → Value {Γ = Γ} (pbuiltin b Ψ σ As' (inj₂ (refl ,, skip p)) ts)


  V-builtin⋆ : ∀{Φ Γ}(b : Builtin)
    → let Ψ ,, As ,, C = SIG b in
      ∀ Ψ' {K} → 
      (σ : SubNf Ψ' Φ)
    → (p : (Ψ' ,⋆ K) ≤C⋆' Ψ)
    → Value {Γ = Γ} (pbuiltin b Ψ' σ [] (inj₁ (skip p ,, refl)) [])
\end{code}

\begin{code}
voidVal : ∀ {Φ}(Γ : Ctx Φ) → Value {Γ = Γ} (con unit)
voidVal Γ = V-con {Γ = Γ} unit
\end{code}

\begin{code}
VTel : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → Tel Γ Δ σ As → Set

data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
\end{code}

\begin{code}
VTel Γ Δ σ []       []        = ⊤
VTel Γ Δ σ (A ∷ As) (t ∷ tel) = Value t × VTel Γ Δ σ As tel

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
BUILTIN addInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i + j))
BUILTIN subtractInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i - j))
BUILTIN multiplyInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  con (integer (i ** j))
BUILTIN divideInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (div i j)))
BUILTIN quotientInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (quot i j)))
BUILTIN remainderInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (rem i j)))
BUILTIN modInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (∣ j ∣ Data.Nat.≟ zero) (error _) (con (integer (mod i j)))
BUILTIN lessThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i <? j) (con (bool true)) (con (bool false))
BUILTIN lessThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt)
  = decIf (i ≤? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.>? j) (con (bool true)) (con (bool false))
BUILTIN greaterThanEqualsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i Builtin.Constant.Type.≥? j) (con (bool true)) (con (bool false))
BUILTIN equalsInteger _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (integer j) ,, tt) =
  decIf (i ≟ j) (con (bool true)) (con (bool false))
BUILTIN concatenate _ (_ ∷ _ ∷ []) (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) =
  con (bytestring (append b b'))
BUILTIN takeByteString _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  con (bytestring (take i b))
BUILTIN dropByteString _ (_ ∷ _ ∷ []) (V-con (integer i) ,, V-con (bytestring b) ,, tt) =
  con (bytestring (drop i b))
BUILTIN sha2-256 _ (_ ∷ []) (V-con (bytestring b) ,, tt) =
  con (bytestring (SHA2-256 b))
BUILTIN sha3-256 _ (_ ∷ []) (V-con (bytestring b) ,, tt) =
  con (bytestring (SHA3-256 b))
BUILTIN verifySignature _ (_ ∷ _ ∷ _ ∷ []) (V-con (bytestring k) ,, V-con (bytestring d) ,, V-con (bytestring c) ,, tt) = VERIFYSIG (verifySig k d c)
BUILTIN equalsByteString _ (_ ∷ _ ∷ []) (V-con (bytestring b) ,, V-con (bytestring b') ,, tt) = con (bool (equals b b'))
BUILTIN ifThenElse _ (_ ∷ t ∷ _ ∷ _) (V-con (bool true)  ,, _) = t
BUILTIN ifThenElse _ (_ ∷ _ ∷ u ∷ _) (V-con (bool false) ,, _) = u
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
data Any {Φ}{Γ}{Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}(P : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set) : ∀{As} → (ts : Tel Γ Δ σ As) → Set where
  here : ∀ {A}{As}{t}{ts} → P t → Any P {As = A ∷ As} (t ∷ ts)
  there : ∀ {A}{As}{t}{ts} → Value t → Any P ts → Any P {As = A ∷ As} (t ∷ ts)
data _—→T_ {Φ}{Γ : Ctx Φ}{Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J} : {As : List (Δ ⊢Nf⋆ *)}
  → Tel Γ Δ σ As → Tel Γ Δ σ As → Set
  
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

  β-wrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → {M : Γ ⊢ _}
    → Value M
    → unwrap (wrap A B M) —→ M

  ξ-unwrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → {M M' : Γ ⊢ μ A B}
    → M —→ M'
    → unwrap M —→ unwrap M'
    
  ξ-wrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → {M M' : Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
    → M —→ M'
    → wrap A B M —→ wrap A B M'

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
    → {ts ts' : Tel Γ Δ σ As}
    → ts —→T ts'
    → builtin bn σ ts —→ builtin bn σ ts'

  tick-pbuiltin : ∀{Φ Γ}{b : Builtin}
      → let Ψ ,, As ,, C = SIG b in
        (σ : SubNf Ψ Φ)
      → {ts : Tel Γ Ψ σ []}
      → pbuiltin b Ψ σ []  (inj₁ (base ,, refl)) ts
        —→ pbuiltin b Ψ σ [] (inj₂ (refl ,, []≤L' _)) ts

  β-pbuiltin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As tel)
      -----------------------------
    → pbuiltin bn _ σ _ (inj₂ (refl ,, base)) tel —→ BUILTIN bn σ tel vtel
    
  ξ-pbuiltin : ∀{Φ Γ} → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → {ts ts' : Tel Γ Δ σ As}
    → ts —→T ts'
    → pbuiltin bn _ σ _ (inj₂ (refl ,, base)) ts —→ pbuiltin bn _ σ _ (inj₂ (refl ,, base)) ts'

  E-·₂ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *} {L : Γ ⊢ A ⇒ B}
    → Value L
    → L · error A —→ error B
  E-·₁ : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}{M : Γ ⊢ A}
    → error (A ⇒ B) · M —→ error B
  E-·⋆ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}{A : Φ ⊢Nf⋆ K}
    → error {Γ = Γ} (Π B) ·⋆ A —→ error (B [ A ]Nf)
  E-unwrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → unwrap (error (μ A B))
        —→ error {Γ = Γ} (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  E-wrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → wrap A B (error _) —→ error {Γ = Γ} (μ A B) 
  E-builtin : ∀{Φ Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
    → (ts : Tel Γ Δ σ As)
    → Any Error ts
    → builtin bn σ ts —→ error (substNf σ C)

  E-pbuiltin : ∀{Φ Γ}(b :  Builtin)
    → let Ψ ,, As ,, C = SIG b in
      (σ : SubNf Ψ Φ)
    → (ts : Tel Γ Ψ σ As)
    → Any Error ts
    → pbuiltin b Ψ σ As (inj₂ (refl ,, base)) ts —→ error (abstractArg As As (inj₂ (refl ,, base)) C σ)

  E-ibuiltin : ∀{Φ Γ}
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      (σ⋆ : SubNf Ψ Φ)
    → (σ : ITel Δ Γ σ⋆)
    → ibuiltin b σ⋆ σ —→ error (substNf σ⋆ C)

  E-ipbuiltin : ∀{Φ Γ}
      (b : Builtin)
    → let Ψ ,, Δ ,, C = ISIG b in
      ∀ Ψ'
    → (Δ' : Ctx Ψ')
    → (p : Δ' ≤C Δ)
      (σ⋆ : SubNf Ψ' Φ)
    → (σ : ITel Δ' Γ σ⋆)
    → ipbuiltin b Ψ' Δ' p σ⋆ σ —→ error (apply⋆ Φ Γ Ψ Ψ' Δ Δ' p C σ⋆ σ)

data _—→T_ {Φ}{Γ}{Δ}{σ} where
  here  : ∀{A}{As}{t t'}{ts : Tel Γ Δ σ As}
    → t —→ t' → (_∷_ {A = A} t ts) —→T (t' ∷ ts)
  there : ∀{A As}{t}{ts ts' : Tel Γ Δ σ As}
    → Value t → ts —→T ts' → (_∷_ {A = A} t ts) —→T (t ∷ ts')

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
  {σ : SubNf Δ Φ}
  {As : List (Δ ⊢Nf⋆ *)}
  (ts : Tel Γ Δ σ As)
  : Set where
  done : VTel Γ Δ σ As ts → TelProgress ts
  step : {ts' : Tel Γ Δ σ As}
    → ts —→T ts'
    → TelProgress ts
    
  error : Any Error ts → TelProgress ts
\end{code}

\begin{code}
progress-·V :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → {t : Γ ⊢ A ⇒ B} → Value t
  → {u : Γ ⊢ A} → Progress u
  → Progress (t · u)
progress-·V v       (step q)        = step (ξ-·₂ v q)
progress-·V v       (error E-error) = step (E-·₂ v)
progress-·V (V-ƛ t) (done w)        = step (β-ƛ w)

progress-· :  ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → {t : Γ ⊢ A ⇒ B} → Progress t
  → {u : Γ ⊢ A} → Progress u
  → Progress (t · u)
progress-· (step p)        q = step (ξ-·₁ p)
progress-· (done (V-ƛ t))  q = progress-·V (V-ƛ t) q
progress-· (error E-error) q = step E-·₁

progress-·⋆ :  ∀{Φ Γ}{K B}{t : Γ ⊢ Π B} → Progress t → (A : Φ ⊢Nf⋆ K)
  → Progress (t ·⋆ A)
progress-·⋆ (step p)        A = step (ξ-·⋆ p)
progress-·⋆ (done (V-Λ t))  A = step β-Λ
progress-·⋆ (error E-error) A = step E-·⋆

progress-unwrap : ∀{Φ Γ K}{A}{B : Φ ⊢Nf⋆ K}{t : Γ ⊢ μ A B}
  → Progress t → Progress (unwrap t)
progress-unwrap (step q) = step (ξ-unwrap q)
progress-unwrap (done (V-wrap v)) = step (β-wrap v)
progress-unwrap {A = A} (error E-error) =
  step (E-unwrap {A = A})

progress-builtin : ∀{Φ Γ} bn
  (σ : SubNf (proj₁ (SIG bn)) Φ)
  (tel : Tel Γ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn))))
  → TelProgress tel
  → Progress (builtin bn σ tel)
progress-builtin bn σ tel (done vtel)                       =
  step (β-builtin bn σ tel vtel)
progress-builtin bn σ tel (step p) = step (ξ-builtin bn σ p)
progress-builtin bn σ tel (error p) = step (E-builtin bn σ tel p)

progress-pbuiltin : ∀{Φ Γ} bn
  (σ : SubNf (proj₁ (SIG bn)) Φ)
  (tel : Tel Γ (proj₁ (SIG bn)) σ (proj₁ (proj₂ (SIG bn))))
  → TelProgress tel
  → Progress (pbuiltin bn _ σ _ (inj₂ (refl ,, base)) tel)
progress-pbuiltin bn σ tel (done vs) = step (β-pbuiltin bn σ tel vs)
progress-pbuiltin bn σ tel (step p)  = step (ξ-pbuiltin bn σ p)
progress-pbuiltin bn σ tel (error e) = step (E-pbuiltin bn σ tel e)

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
  → TelProgress {As = A ∷ As} (t ∷ tel)
progressTelCons n (step p)  q           = step (here p)
progressTelCons n (error p) q           = error (here p)
progressTelCons n (done v)  (done vtel) = done (v ,, vtel)
progressTelCons n (done v)  (step p)    = step (there v p)
progressTelCons n (done v)  (error p)   = error (there v p)

progressTel : ∀ {Φ Γ} → NoVar Γ → ∀{Δ}
  → {σ : SubNf Δ Φ}
  → {As : List (Δ ⊢Nf⋆ *)}
  → (tel : Tel Γ Δ σ As)
  → TelProgress tel
progressTel p {As = []}     []        = done tt
progressTel p {As = A ∷ As} (t ∷ tel) =
  progressTelCons p (progress p t) (progressTel p tel)

progress-wrap :  ∀{Φ Γ} → NoVar Γ  → ∀{K}
   → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : Φ ⊢Nf⋆ K}
   → {M : Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
   → Progress M → Progress (wrap A B M)
progress-wrap n (step p)        = step (ξ-wrap p)
progress-wrap n (done v)        = done (V-wrap v)
progress-wrap n (error E-error) = step E-wrap

progress p (` x)                = ⊥-elim (noVar p x)
progress p (ƛ M)                = done (V-ƛ M)
progress p (M · N)              = progress-· (progress p M) (progress p N)
progress p (Λ M)                = done (V-Λ M)
progress p (M ·⋆ A)             = progress-·⋆ (progress p M) A
progress p (wrap A B M) = progress-wrap p (progress p M)
progress p (unwrap M)          = progress-unwrap (progress p M)
progress p (con c)              = done (V-con c)
progress p (builtin bn σ ts)     = progress-builtin bn σ ts (progressTel p ts)
progress p (pbuiltin b .(proj₁ (SIG b)) σ .[] (inj₁ (base ,, refl)) ts) =
  step (tick-pbuiltin σ)
progress p (pbuiltin b Ψ' σ As' (inj₁ (skip q ,, refl)) []) =
  done (V-builtin⋆ b Ψ' σ q)
progress p (pbuiltin b Ψ' σ _ (inj₂ (refl ,, base)) ts) =
  progress-pbuiltin b σ ts (progressTel p ts)
progress p (pbuiltin b Ψ' σ As' (inj₂ (refl ,, skip r)) ts) =
  done (V-builtin b σ _ _ r ts)
progress p (ibuiltin b σ⋆ σ) = step (E-ibuiltin b σ⋆ σ)
progress p (ipbuiltin b Ψ' Δ' q σ⋆ σ) = step (E-ipbuiltin b Ψ' Δ' q σ⋆ σ)
progress p (error A)            = error E-error

--

open import Data.Empty

-- progress is disjoint:


-- a value cannot make progress

val-red : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢ σ} → Value t → ¬ (Σ (Γ ⊢ σ) (t —→_))
val-red (V-wrap p) (.(wrap _ _ _) ,, ξ-wrap q) = val-red p (_ ,, q)

valT-redT : ∀ {Φ Γ Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel Γ Δ σ As} → VTel Γ Δ σ As ts → ¬ Σ (Tel Γ Δ σ As) (ts —→T_)
valT-redT (v ,, vs) (.(_ ∷ _) ,, here p)    = val-red v (_ ,, p)
valT-redT (v ,, vs) (.(_ ∷ _) ,, there w p) = valT-redT vs (_ ,, p)

-- a value cannot be an error

val-err : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢ σ} → Value t → ¬ (Error t)
val-err () E-error

valT-errT : ∀ {Φ Γ Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel Γ Δ σ As} → VTel Γ Δ σ As ts → ¬ (Any Error ts)
valT-errT (v ,, vs) (here p)    = val-err v p
valT-errT (v ,, vs) (there w p) = valT-errT vs p

-- an error cannot make progress

red-err : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t : Γ ⊢ σ} → Σ (Γ ⊢ σ) (t —→_) → ¬ (Error t)
red-err () E-error

redT-errT : ∀ {Φ Γ Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As : List (Δ ⊢Nf⋆ *)}
  → {ts : Tel Γ Δ σ As} → Σ (Tel Γ Δ σ As) (ts —→T_) → ¬ (Any Error ts)
redT-errT (.(_ ∷ _) ,, here p)    (here q)    = red-err (_ ,, p) q
redT-errT (.(_ ∷ _) ,, there v p) (here q)    = val-err v q
redT-errT (.(_ ∷ _) ,, here p)    (there w q) = val-red w (_ ,, p)
redT-errT (.(_ ∷ _) ,, there v p) (there w q) = redT-errT (_ ,, p) q

-- values are unique for a term
valUniq : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}(t : Γ ⊢ A) → (v v' : Value t) → v ≡ v'
valUniq .(ƛ _)         (V-ƛ _)    (V-ƛ _)     = refl
valUniq .(Λ _)         (V-Λ _)    (V-Λ _)     = refl
valUniq .(wrap _ _ _) (V-wrap v) (V-wrap v') = cong V-wrap (valUniq _ v v')
valUniq .(con cn)      (V-con cn) (V-con .cn) = refl

-- telescopes of values are unique for that telescope
vTelUniq : ∀ {Φ} Γ Δ → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)(As : List (Δ ⊢Nf⋆ *))
  → (tel : Tel Γ Δ σ As)
  → (vtel vtel' : VTel Γ Δ σ As tel)
  → vtel ≡ vtel'
vTelUniq Γ Δ σ [] [] vtel vtel' = refl
vTelUniq Γ Δ σ (A ∷ As) (t ∷ tel) (v ,, vtel) (v' ,, vtel') =
  cong₂ _,,_ (valUniq t v v') (vTelUniq Γ Δ σ As tel vtel vtel') 

-- exclusive or
_xor_ : Set → Set → Set
A xor B = (A ⊎ B) × ¬ (A × B)

infixr 2 _xor_

-- a term cannot make progress and be a value

notboth : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → ¬ (Value t × Σ (∅ ⊢ σ) (t —→_))
notboth (v ,, p) = val-red v p

-- term cannot make progress and be error

notboth' : {σ : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ σ} → ¬ (Σ (∅ ⊢ σ) (t —→_) × Error t)
notboth' (p ,, e) = red-err p e

-- armed with this, we can upgrade progress to an xor

progress-xor : {σ : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ σ)
  → Value t xor (Σ (∅ ⊢ σ) (t —→_)) xor Error t
progress-xor t with progress _ t
progress-xor t | step p  = (inj₂ ((inj₁ (_ ,, p)) ,, λ{(p ,, e) → red-err p e})) ,, λ { (v ,, inj₁ p ,, q) → val-red v p ; (v ,, inj₂ e ,, q) → val-err v e}
progress-xor t | done v  = (inj₁ v) ,, (λ { (v' ,, inj₁ p ,, q) → val-red v p ; (v' ,, inj₂ e ,, q) → val-err v e})
progress-xor t | error e = (inj₂ ((inj₂ e) ,, (λ { (p ,, e) → red-err p e}))) ,, λ { (v ,, q) → val-err v e }

-- the reduction rules are deterministic
det : ∀{Φ Γ}{σ : Φ ⊢Nf⋆ *}{t t' t'' : Γ ⊢ σ}
  → (p : t —→ t')(q : t —→ t'') → t' ≡ t''
detT : ∀{Φ}{Γ}{Δ}{σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}{As}{ts ts' ts'' : Tel Γ Δ σ As}
    → (p : ts —→T ts')(q : ts —→T ts'') → ts' ≡ ts''

det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ w q) = ⊥-elim (val-red w (_ ,, p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (val-red v (_ ,, q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (val-red w (_ ,, p))
det (ξ-·⋆ p) (ξ-·⋆ q) = cong (_·⋆ _) (det p q)
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (val-red v (_ ,, q))
det (β-ƛ v) (β-ƛ w) = refl
det β-Λ β-Λ = refl
det (β-wrap p) (β-wrap q) = refl
det (β-wrap p) (ξ-unwrap q) = ⊥-elim (val-red (V-wrap p) (_ ,, q))
det (ξ-unwrap p) (β-wrap q) = ⊥-elim (val-red (V-wrap q) (_ ,, p))
det (ξ-unwrap p) (ξ-unwrap q) = cong unwrap (det p q)
det (ξ-wrap p) (ξ-wrap q) = cong (wrap _ _) (det p q)
det (β-builtin bn σ ts vs) (β-builtin .bn .σ .ts ws) =
  cong (BUILTIN bn σ ts) (vTelUniq _ _ σ _ ts vs ws)
det (β-builtin bn σ ts vs) (ξ-builtin .bn .σ p) =
  ⊥-elim (valT-redT vs (_ ,, p))
det (ξ-builtin bn σ p) (β-builtin .bn .σ ts vs) =
  ⊥-elim (valT-redT vs (_ ,, p))
det (ξ-builtin bn σ p) (ξ-builtin .bn .σ p') = cong (builtin bn σ) (detT p p')
det (β-builtin .bn .σ ts vs) (E-builtin bn σ ts' p) = ⊥-elim (valT-errT vs p)
det (ξ-builtin bn σ p) (E-builtin bn .σ ts q) = ⊥-elim (redT-errT (_ ,, p) q)
det (E-builtin bn σ ts p) (E-builtin bn σ ts q) = refl
det (E-builtin bn σ ts p) (β-builtin .bn .σ .ts vs) = ⊥-elim (valT-errT vs p)
det (E-builtin bn σ ts p) (ξ-builtin .bn .σ q) = ⊥-elim (redT-errT (_ ,, q) p)
det E-·₁ (ξ-·₁ ())
det (E-·₂ v) (ξ-·₁ p) = ⊥-elim (val-red v (_ ,, p))
det (E-·₂ v) (E-·₂ w) = refl
det (E-·₂ ()) E-·₁
det (ξ-·₁ p) (E-·₂ v) = ⊥-elim (val-red v (_ ,, p))
det E-·₁ (E-·₂ ())
det E-·₁ E-·₁ = refl
det E-·⋆ E-·⋆ = refl
det E-unwrap E-unwrap = refl
det E-wrap E-wrap = refl
det (E-ibuiltin b σ⋆ σ) (E-ibuiltin .b .σ⋆ .σ) = refl
det (E-ipbuiltin b Ψ' Δ' p₁ σ⋆ σ) (E-ipbuiltin .b .Ψ' .Δ' .p₁ .σ⋆ .σ) = refl

detT (here p)    (here q)    = cong (_∷ _) (det p q)
detT (here p)    (there w q) = ⊥-elim (val-red w (_ ,, p))
detT (there v p) (here q)    = ⊥-elim (val-red v (_ ,, q))
detT (there v p) (there w q) = cong (_ ∷_) (detT p q)

-- some auxiliary functions

vTel++ : ∀ {Φ Γ Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {As As' : List (Δ ⊢Nf⋆ *)}
  → (ts : Tel Γ Δ σ As)
  → (ts' : Tel Γ Δ σ As')
  → VTel Γ Δ σ As ts
  → VTel Γ Δ σ As' ts'
  → VTel Γ Δ σ (As ++ As') (ts ++T ts')
vTel++ []       ts' vs        vs' = vs'
vTel++ (t ∷ ts) ts' (v ,, vs) vs' = v ,, vTel++ ts ts' vs vs' 

vTel:< : ∀ {Φ Γ Δ}
  → {σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K}
  → {As : List (Δ ⊢Nf⋆ *)}
  → {A : Δ ⊢Nf⋆ *}
  → (ts : Tel Γ Δ σ As)
  → (t : Γ ⊢ substNf σ A)
  → VTel Γ Δ σ As ts
  → Value t
  → VTel Γ Δ σ (As :<L A) (ts :<T t)
vTel:< []        t vs v = v ,, tt
vTel:< (t' ∷ ts) t (v' ,, vs) v = v' ,, vTel:< ts t vs v
