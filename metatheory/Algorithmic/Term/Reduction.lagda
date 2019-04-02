\begin{code}
module Algorithmic.Term.Reduction where
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
open import Algorithmic.Term
open import Algorithmic.Term.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf size⋆
open import Utils
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
data Error :  ∀ {Γ} {A : ∥ Γ ∥ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  E-error : ∀{Γ}{A : ∥ Γ ∥ ⊢Nf⋆ *} → Error (error {Γ} A)
\end{code}

\begin{code}
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
BUILTIN subtractInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  subtractInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (i - j)
... | yes r = just (con (integer s (i - j) r))
... | no ¬p = nothing
BUILTIN multiplyInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  multiplyInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (i ** j)
... | yes r = just (con (integer s (i ** j) r))
... | no ¬p = nothing
BUILTIN divideInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  divideInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (div i j)
... | yes r = just (con (integer s (div i j) r))
... | no ¬r = nothing
BUILTIN quotientInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  quotientInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (quot i j)
... | yes r = just (con (integer s (quot i j) r))
... | no ¬r = nothing
BUILTIN remainderInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  remainderInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (rem i j)
... | yes r = just (con (integer s (rem i j) r))
... | no ¬r = nothing
BUILTIN modInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  modInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with boundedI? s (mod i j)
... | yes r = just (con (integer s (mod i j) r))
... | no ¬r = nothing
BUILTIN lessThanInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  lessThanInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with i Builtin.Constant.Type.<? j
... | yes _ = just true
... | no _  = just false
BUILTIN lessThanEqualsInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  lessThanEqualsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with i ≤? j
... | yes _ = just true
... | no _  = just false
BUILTIN greaterThanInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  greaterThanInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with i Builtin.Constant.Type.>? j
... | yes _ = just true
... | no _  = just false
BUILTIN greaterThanEqualsInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  greaterThanEqualsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with i Builtin.Constant.Type.≥? j
... | yes _ = just true
... | no _  = just false
BUILTIN equalsInteger σ vtel with nf (embNf (σ Z))
BUILTIN
  equalsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt)
  | size⋆ s
  with i ≟ j
... | yes _ = just true
... | no _  = just false
BUILTIN resizeInteger σ vtel with nf (embNf (σ Z)) | nf (embNf (σ (S Z)))
BUILTIN
  resizeInteger
  σ
  (_ ,, V-con (size s') ,, _ ,, V-con (integer s i p) ,, tt)
  | size⋆ s'
  | size⋆ s
  with boundedI? s' i
... | yes r = just (con (integer s' i r))
... | no ¬r = nothing
BUILTIN sizeOfInteger σ vtel with nf (embNf (σ Z))
BUILTIN sizeOfInteger σ (_ ,, V-con (integer s i x) ,, tt) | .(size⋆ s) =
  just (con (size s))
BUILTIN intToByteString σ vtel with nf (embNf (σ Z)) | nf (embNf (σ (S Z)))
BUILTIN
  intToByteString
  σ
  (_ ,, V-con (size s) ,, _ ,, V-con (integer s' i p) ,, tt)
  | size⋆ s
  | size⋆ s' with boundedI? s i
... | no _  = nothing
... | yes q with boundedB? s (int2ByteString i)
... | yes r = just (con (bytestring s (int2ByteString i) r))
... | no _  = nothing
-- ^ should be impossible if we prove something about int2ByteString
BUILTIN concatenate σ vtel with nf (embNf (σ Z))
BUILTIN
  concatenate
  σ
  (_ ,, V-con (bytestring s b p) ,, _ ,, V-con (bytestring .s b' q) ,, tt)
  | size⋆ s
  with boundedB? s (append b b')
... | yes r = just (con (bytestring s (append b b') r))
... | no ¬r = nothing 

BUILTIN takeByteString σ vtel with nf (embNf (σ Z)) | nf (embNf (σ (S Z)))
BUILTIN
  takeByteString
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (bytestring s' b q) ,, tt)
  | .(size⋆ s')
  | size⋆ s
  with boundedB? s' (take i b)
... | yes r = just (con (bytestring s' (take i b) r))
... | no r = nothing
-- ^ this is impossible but we haven't proved that take cannot
-- increase the length
BUILTIN dropByteString σ vtel with nf (embNf (σ Z)) | nf (embNf (σ (S Z)))
BUILTIN
  dropByteString
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (bytestring s' b q) ,, tt)
  | size⋆ s'
  | size⋆ s with boundedB? s' (drop i b)
... | yes r = just (con (bytestring s' (drop i b) r))
... | no ¬r = nothing
-- ^ this is impossible but we haven't proved that drop cannot
-- increase the length
BUILTIN sha2-256 σ vtel with nf (embNf (σ Z))
BUILTIN
  sha2-256
  σ
  (_ ,, V-con (bytestring s b p) ,, tt)
  | size⋆ s with boundedB? 32 (SHA2-256 b)
... | yes q = just (con (bytestring 32 (SHA2-256 b) q))
... | no  _ = nothing
-- ^ should be impossible
BUILTIN sha3-256 σ vtel with nf (embNf (σ Z))
BUILTIN
  sha3-256
  σ
  (_ ,, V-con (bytestring s b p) ,, tt)
  | size⋆ s with boundedB? 32 (SHA3-256 b)
... | yes q = just (con (bytestring 32 (SHA3-256 b) q))
... | no  _ = nothing
-- ^ should be impossible
BUILTIN verifySignature σ vtel with
  nf (embNf (σ Z))
  | nf (embNf (σ (S Z)))
  | nf (embNf (σ (S (S Z))))
BUILTIN
  verifySignature
  σ
  (  _ ,, V-con (bytestring s k p)
  ,, _ ,, V-con (bytestring s' d p')
  ,, _ ,, V-con (bytestring s'' c p'')
  ,, tt)
  | size⋆ s''
  | size⋆ s'
  | size⋆ s
  with verifySig k d c
... | just Bool.true  = just true
... | just Bool.false = just false
... | nothing = nothing
BUILTIN resizeByteString σ vtel with nf (embNf (σ Z)) | nf (embNf (σ (S Z)))
BUILTIN
  resizeByteString
  σ
  (_ ,, V-con (size s) ,, _ ,, V-con (bytestring s' b p) ,, tt)
  | size⋆ s
  | size⋆ s'
  with boundedB? s b
... | yes q = just (con (bytestring s b q))
... | no  _ = nothing
BUILTIN equalsByteString σ vtel with nf (embNf (σ Z))
BUILTIN
  equalsByteString
  σ
  (_ ,, V-con (bytestring s b p) ,, _ ,, V-con (bytestring .s b' q) ,, tt)
  | size⋆ s
  with equals b b'
... | Bool.true  = just true
... | Bool.false = just false
\end{code}


# recontructing the telescope after a reduction step

\begin{code}
reconstTel : ∀{Γ Δ As} Bs Ds
    → (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (vtel : VTel Γ Δ σ Bs)
    → ∀{C}(t' : Γ ⊢ substNf σ C)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → Tel Γ Δ σ As
reconstTel [] Ds σ vtel t' refl tel' = t' ,, tel'
reconstTel (B ∷ Bs) Ds σ (X ,, VX ,, vtel) t' refl tel' =
  X ,, reconstTel Bs Ds σ vtel t' refl tel'
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

  E-·₁ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → Error L
      -----------------
    → L · M —→ error _

  E-·₂ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → Error M
      -----------------
    → L · M —→ error _

  ξ-·⋆ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

  E-·⋆ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{L : Γ ⊢ Π B}{A}
    → Error L
      -----------------
    → L ·⋆ A —→ error _

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

  E-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → {M : Γ ⊢ ne (μ1 · pat · arg)}
    → Error M
    → unwrap1 M —→ error _


  β-builtin : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → (vtel : VTel Γ Δ σ As)
      -----------------------------
    → builtin bn σ tel —→ maybe id (error _) (BUILTIN bn σ vtel)

  ξ-builtin : ∀{Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (vtel : VTel Γ Δ σ Bs)
    → ∀{C}{t t' : Γ ⊢ substNf σ C}
    → t —→ t'
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → builtin bn σ tel
      —→
      builtin bn σ (reconstTel Bs Ds σ vtel t' p tel')

  E-builtin : ∀{Γ}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {K} → Δ ∋⋆ K → ∥ Γ ∥ ⊢Nf⋆ K)
    → (tel : Tel Γ Δ σ As)
    → ∀ Bs Ds
    → (vtel : VTel Γ Δ σ Bs)
    → ∀{C}{t : Γ ⊢ substNf σ C}
    → Error t
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel Γ Δ σ Ds)
    → builtin bn σ tel
      —→
      error _


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
  error :
      Error M
      -------
    → Progress M
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
  error : ∀ Bs Ds
    → VTel Γ Δ σ Bs
    → ∀{C}{t  : Γ ⊢ substNf σ C}
    → Error t
    → Bs ++ (C ∷ Ds) ≡ As
    → Tel Γ Δ σ Ds
    → TelProgress tel
   
    
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
progressTel {As = A ∷ As} (t ,, tel) | error E = error [] As tt E refl tel
progressTel {As = A ∷ As} (t ,, tel) | step p  = step [] As tt p refl tel
progressTel {As = A ∷ As} (t ,, tel) | done vt with progressTel tel
progressTel {As = A ∷ As} (t ,, tel) | done vt | done vtel =
  done (t ,, vt ,, vtel)
progressTel {As = A ∷ As} (t ,, tel) | done vt | step Bs Ds vtel p q tel' =
  step (A ∷ Bs) Ds (t ,, vt ,, vtel) p (cong (A ∷_) q) tel'
progressTel {As = A ∷ As} (t ,, tel) | done vt | error Bs Ds vtel E q tel' = error (A ∷ Bs) Ds (t ,, vt ,, vtel) E (cong (A ∷_) q) tel'


progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
...                   | error EM  = step (E-·₁ EM)
progress (M · N)      | step p = step (ξ-·₁ p)
progress (.(ƛ _) · N) | done V-ƛ with progress N
...                              | error EN  = step (E-·₂ EN)
progress (.(ƛ _) · N) | done V-ƛ | step p  = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step (β-ƛ VN)
progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
...               | error EM  = step (E-·⋆ EM)
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap1 pat arg term) = done V-wrap1
progress (unwrap1 M)       with progress M
...                  | error EM  = step (E-unwrap1 EM)
progress (unwrap1 M) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (con (integer s i x))    = done (V-con _)
progress (con (bytestring s b x)) = done (V-con _)
progress (con (TermCon.size s))   = done (V-con _)
progress (builtin bn σ X) with progressTel X
progress (builtin bn σ X) | done VX = step (β-builtin bn σ X VX)
progress (builtin bn σ X) | step Bs Ds vtel p q tel' =
  step (ξ-builtin bn σ X Bs Ds vtel p q tel')
progress (builtin bn σ X) | error Bs Ds vtel p q tel' =
  step (E-builtin bn σ X Bs Ds vtel p q tel')
progress (error A)        = error E-error
