\begin{code}
module TermIndexedBySyntacticType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Term.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to substEq)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_; ,_ to ,,_)
open import Data.List hiding ([_]; take; drop)
open import Function
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
open import Data.Integer renaming (_*_ to _**_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Maybe
open import Agda.Builtin.Int
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_)
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap1 : ∀{Γ K}
   → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∥ Γ ∥ ⊢⋆ K}
   → {term : Γ ⊢ pat · (μ1 · pat) · arg}
   → Value (wrap1 pat arg term)

  V-con : ∀{Γ}{n}{tcn : TyCon}
    → (cn : TermCon (con tcn (size⋆ n)))
    → Value (con {Γ} cn)

\end{code}

## BUILTIN
\begin{code}
VTel : ∀ Γ Δ → ⋆.Sub ∥ Δ ∥ ∥ Γ ∥ → List (∥ Δ ∥ ⊢⋆ *) → Set
VTel Γ Δ σ [] = ⊤
VTel Γ Δ σ (A ∷ As) = Σ (Γ ⊢ ⋆.subst σ A) λ t → Value t × VTel Γ Δ σ As

BUILTIN : ∀{Γ Γ'}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn Γ in
      (σ : ⋆.Sub ∥ Δ ∥ ∥ Γ ∥)
    → (vtel : VTel Γ Δ σ As)
    → (σ' : ⋆.Sub ∥ Γ ∥ ∥ Γ' ∥)
      -----------------------------
    → Maybe (Γ' ⊢ ⋆.subst σ' (⋆.subst σ C))
BUILTIN addInteger σ vtel σ' with σ Z
BUILTIN
  addInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (i + j)
... | yes r = just (con (integer s (i + j) r))
... | no ¬r = nothing
BUILTIN subtractInteger σ vtel σ' with σ Z
BUILTIN
  subtractInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (i - j)
... | yes r = just (con (integer s (i - j) r))
... | no ¬p = nothing
BUILTIN multiplyInteger σ vtel σ' with σ Z
BUILTIN
  multiplyInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (i ** j)
... | yes r = just (con (integer s (i ** j) r))
... | no ¬p = nothing
BUILTIN divideInteger σ vtel σ' with σ Z
BUILTIN
  divideInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s (pos 0) q) ,, tt) σ'
  | .(size⋆ s)
  = nothing
BUILTIN
  divideInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (div i j)
... | yes r = just (con (integer s (div i j) r))
... | no ¬r = nothing
BUILTIN quotientInteger σ vtel σ' with σ Z
BUILTIN
  quotientInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s (pos 0) q) ,, tt) σ'
  | .(size⋆ s)
  = nothing
BUILTIN
  quotientInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (quot i j)
... | yes r = just (con (integer s (quot i j) r))
... | no ¬r = nothing
BUILTIN remainderInteger σ vtel σ' with σ Z
BUILTIN
  remainderInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s (pos 0) q) ,, tt) σ'
  | .(size⋆ s)
  = nothing
BUILTIN
  remainderInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (rem i j)
... | yes r = just (con (integer s (rem i j) r))
... | no ¬r = nothing
BUILTIN modInteger σ vtel σ' with σ Z
BUILTIN
  modInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s (pos 0) q) ,, tt) σ'
  | .(size⋆ s)
  = nothing
BUILTIN
  modInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with boundedI? s (mod i j)
... | yes r = just (con (integer s (mod i j) r))
... | no ¬r = nothing
BUILTIN lessThanInteger σ vtel σ' with σ Z
BUILTIN
  lessThanInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with i <? j
... | yes _ = just true
... | no _  = just false
BUILTIN lessThanEqualsInteger σ vtel σ' with σ Z
BUILTIN
  lessThanEqualsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with i ≤? j
... | yes _ = just true
... | no _  = just false
BUILTIN greaterThanInteger σ vtel σ' with σ Z
BUILTIN
  greaterThanInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with i >? j
... | yes _ = just true
... | no _  = just false 
BUILTIN greaterThanEqualsInteger σ vtel σ' with σ Z
BUILTIN
  greaterThanEqualsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with i ≥? j
... | yes _ = just true
... | no _  = just false
BUILTIN equalsInteger σ vtel σ' with σ Z
BUILTIN
  equalsInteger
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (integer .s j q) ,, tt) σ'
  | .(size⋆ s)
  with i ≟ j
... | yes _ = just true
... | no _  = just false
BUILTIN resizeInteger σ vtel σ' with σ Z | σ (S Z)
BUILTIN
  resizeInteger
  σ
  (_ ,, V-con (size s') ,, _ ,, V-con (integer s i p) ,, tt) σ'
  | .(size⋆ s')
  | .(size⋆ s)
  with boundedI? s' i
... | yes r = just (con (integer s' i r))
... | no ¬r = nothing
BUILTIN sizeOfInteger σ vtel σ' with σ Z
BUILTIN sizeOfInteger σ (_ ,, V-con (integer s i x) ,, tt) σ' | .(size⋆ s) =
  just (con (size s))
BUILTIN concatenate σ vtel σ' with σ Z
BUILTIN
  concatenate
  σ
  (_ ,, V-con (bytestring s b p) ,, _ ,, V-con (bytestring .s b' q) ,, tt) σ'
  | .(size⋆ s)
  with boundedB? s (append b b')
... | yes r = just (con (bytestring s (append b b') r))
... | no ¬r = nothing 
BUILTIN takeByteString σ vtel σ' with σ Z | σ (S Z)
BUILTIN
  takeByteString
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (bytestring s' b q) ,, tt) σ'
  | .(size⋆ s')
  | .(size⋆ s)
  with boundedB? s' (take i b)
... | yes r = just (con (bytestring s' (take i b) r))
... | no r = nothing
-- ^ this is impossible but we haven't proved that take cannot
-- increase the length
BUILTIN dropByteString σ vtel σ' with σ Z | σ (S Z) 
BUILTIN
  dropByteString
  σ
  (_ ,, V-con (integer s i p) ,, _ ,, V-con (bytestring s' b q) ,, tt) σ'
  | .(size⋆ s')
  | .(size⋆ s) with boundedB? s' (drop i b)
... | yes r = just (con (bytestring s' (drop i b) r))
... | no ¬r = nothing
-- ^ this is impossible but we haven't proved that drop cannot
-- increase the length
\end{code}

# recontructing the telescope after a reduction step

\begin{code}
reconstTel : ∀{Δ As} Bs Ds
    →  (σ : ⋆.Sub ∥ Δ ∥ ∥ ∅ ∥)
    → (vtel : VTel ∅ Δ σ Bs)
    → ∀{C}(t' : ∅ ⊢ ⋆.subst σ C)
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel ∅ Δ σ Ds)
    → Tel ∅ Δ σ As
reconstTel [] Ds σ vtel t' refl tel' = t' ,, tel'
reconstTel (B ∷ Bs) Ds σ (X ,, VX ,, vtel) t' refl tel' =
  X ,, reconstTel Bs Ds σ vtel t' refl tel'
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Γ B}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A
    
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ}{B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}{N : Γ ,⋆ * ⊢ B}{W}
      ----------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  β-wrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {term : Γ ⊢ pat · (μ1 · pat) · arg}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {M M' : Γ ⊢ μ1 · pat · arg}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'


  β-builtin : ∀{Γ'}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn ∅ in
      (σ : ⋆.Sub ∥ Δ ∥ ∥ ∅ ∥)
    → (tel : Tel ∅ Δ σ As)
    → (vtel : VTel ∅ Δ σ As)
    → (σ' : ⋆.Sub ∥ ∅ ∥ ∥ Γ' ∥)
      -----------------------------
    → builtin {Γ'} bn σ tel σ' —→ maybe id (error _) (BUILTIN bn σ vtel σ')

  ξ-builtin : ∀{Γ'}  → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn ∅ in
      (σ : ⋆.Sub ∥ Δ ∥ ∥ ∅ ∥)
    → (tel : Tel ∅ Δ σ As)
    → (σ' : ⋆.Sub ∥ ∅ ∥ ∥ Γ' ∥)
    → ∀ Bs Ds
    → (vtel : VTel ∅ Δ σ Bs)
    → ∀{C}{t t' : ∅ ⊢ ⋆.subst σ C}
    → t —→ t'
    → (p : Bs ++ (C ∷ Ds) ≡ As)
    → (tel' : Tel ∅ Δ σ Ds)
    → builtin {Γ'} bn σ tel σ'
      —→
      builtin {Γ'} bn σ (reconstTel Bs Ds σ vtel t' p tel') σ'
\end{code}


\begin{code}
data Progress {A : ∅ ⊢⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀ {N}
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

data TelProgress {Γ}{Δ}{σ : ⋆.Sub ∥ Δ ∥ ∥ Γ ∥}{As : List (∥ Δ ∥ ⊢⋆ *)}(tel : Tel Γ Δ σ As) : Set where
   done : VTel Γ Δ σ As → TelProgress tel
   step : ∀ Bs Ds
     → VTel Γ Δ σ Bs
     → ∀{C}{t t' : Γ ⊢ ⋆.subst σ C}
     → t —→ t'
     → Bs ++ (C ∷ Ds) ≡ As
     → Tel Γ Δ σ Ds
     → TelProgress tel
   error : TelProgress tel

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progressTel : ∀ {Δ}{σ : ⋆.Sub ∥ Δ ∥ ∥ ∅ ∥}{As : List (∥ Δ ∥ ⊢⋆ *)}
  → (tel : Tel ∅ Δ σ As) → TelProgress tel

progressTel {As = []}    tel = done tt
progressTel {As = A ∷ As} (t ,, tel) with progress t
progressTel {σ = _} {A ∷ As} (t ,, tel) | step p = step [] As tt p refl tel
progressTel {σ = _} {A ∷ As} (t ,, tel) | done vt with progressTel tel
progressTel {σ = _} {A ∷ As} (t ,, tel) | done vt | done vtel =
  done (t ,, vt ,, vtel)
progressTel {σ = _} {A ∷ As} (t ,, tel) | done vt | step Bs Ds vtel p refl tel' =
  step (A ∷ Bs) Ds (t ,, vt ,, vtel) p refl tel'
progressTel {σ = _} {A ∷ As} (t ,, tel) | done vt | error = error
progressTel {σ = _} {A ∷ As} (t ,, tel) | error = error

progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | error = error
...                   | step p  = step (ξ-·₁ p)
progress (.(ƛ _) · M) | done V-ƛ with progress M
progress (.(ƛ _) · M) | done V-ƛ | step p = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · M) | done V-ƛ | done VM = step (β-ƛ VM)
progress (.(ƛ _) · M) | done V-ƛ | error = error
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (M ·⋆ A) | error = error
progress (wrap1 _ _ t) = done V-wrap1
progress (unwrap1 t) with progress t
progress (unwrap1 t) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (unwrap1 t) | error = error
progress (conv p t) = error
progress (con (integer s i p)) = done (V-con _)
progress (con (bytestring s x p)) = done (V-con _)
progress (con (size s)) = done (V-con _)
progress (builtin bn σ X σ') with progressTel X
progress (builtin bn σ X σ') | done VX = step (β-builtin bn σ X VX σ')
progress (builtin bn σ X σ') | step Bs Ds vtel p q tel' =
  step (ξ-builtin bn σ X σ' Bs Ds vtel p q tel')
progress (builtin bn σ X σ') | error          = error
progress (error A) = error


-- does this lose the trace of the progress?
-- perhaps we should instead, return either a completed VTel,
-- or a step and the pieces, or fail, maybe inductively defined

progressTelSilent : ∀ Δ (σ : ⋆.Sub ∥ Δ ∥ ∥ ∅ ∥)(G : List (∥ Δ ∥ ⊢⋆ *))
  → Tel ∅ Δ σ G
  → Maybe (Σ (List (∥ Δ ∥ ⊢⋆ *)) λ G1 →
    Σ (List (∥ Δ ∥ ⊢⋆ *)) λ G2 → 
    G1 ++ G2 ≡ G
    ×
    VTel ∅ Δ σ G1
    ×
    Tel ∅ Δ σ G2)
    
progressTelSilent Δ σ [] tt = just ([] ,, [] ,, refl ,, tt ,, tt)
progressTelSilent Δ σ (A ∷ G) (t ,, tel) with progress t
progressTelSilent Δ σ (A ∷ G) (t ,, tel) | step {N = N} p =
  just ([] ,, A ∷ G ,, refl ,, tt ,, N ,, tel)
progressTelSilent Δ σ (A ∷ G) (t ,, tel) | done v with progressTelSilent Δ σ G tel
... | just (G1 ,, G2 ,, refl ,, vtel ,, tel') = just (A ∷ G1 ,, G2 ,, refl ,, (t ,, v ,, vtel) ,, tel')
... | nothing = nothing
progressTelSilent Δ σ (x ∷ G) (t ,, tel) | unhandled = nothing
\end{code}
