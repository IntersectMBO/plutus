\begin{code}
module Declarative.Erasure where
\end{code}

\begin{code}
open import Declarative
open import Type.RenamingSubstitution as T
open import Untyped
open import Untyped.RenamingSubstitution as U
\end{code}

\begin{code}
open import Type
open import Declarative
open import Builtin
open import Utils
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢⋆_ ` con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
  renaming (TermCon to TyTermCon)

open import Data.Nat
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using ([]; _∷_;_++_)
open import Data.List using (List;length;[];_∷_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (proj₁;proj₂)

len : ∀{Φ} → Ctx Φ → ℕ
len ∅        = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

lemma : (b : Builtin)
  → len⋆ (proj₁ (SIG b)) + length (proj₁ (proj₂ (SIG b))) ≡ arity b
lemma addInteger = refl
lemma subtractInteger = refl
lemma multiplyInteger = refl
lemma divideInteger = refl
lemma quotientInteger = refl
lemma remainderInteger = refl
lemma modInteger = refl
lemma lessThanInteger = refl
lemma lessThanEqualsInteger = refl
lemma greaterThanInteger = refl
lemma greaterThanEqualsInteger = refl
lemma equalsInteger = refl
lemma concatenate = refl
lemma takeByteString = refl
lemma dropByteString = refl
lemma sha2-256 = refl
lemma sha3-256 = refl
lemma verifySignature = refl
lemma equalsByteString = refl
lemma ifThenElse = refl

lemma≤ : (b : Builtin) → len⋆ (proj₁ (SIG b)) + length (proj₁ (proj₂ (SIG b))) ≤‴ arity b
lemma≤ b rewrite lemma b = ≤‴-refl

eraseVar : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero 
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢⋆ *} → TyTermCon A → TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s
eraseTC (bool b)       = bool b 
eraseTC (char c)       = char c
eraseTC unit           = unit

eraseTel⋆ : ∀{Φ}(Γ : Ctx Φ)(Δ : Ctx⋆) → Untyped.Tel (len⋆ Δ) (len Γ) 
eraseTel⋆ _ ∅  = []
eraseTel⋆ Γ (Δ ,⋆ K) = eraseTel⋆ Γ Δ :< con unit

eraseTel : ∀{Φ Γ Δ}{σ : T.Sub Δ Φ}{As : List (Δ ⊢⋆ *)}
  → Declarative.Tel Γ Δ σ As
  → Untyped.Tel (length As) (len Γ) 
erase : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → len Γ ⊢

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = ƛ (U.weaken (erase t))
erase (t ·⋆ A)          = erase t · plc_dummy
erase (wrap A B t)      = erase t
erase (unwrap t)        = erase t
erase (conv p t)        = erase t
erase {Γ = Γ} (con t)   = con (eraseTC {Γ = Γ} t)
erase {Γ = Γ} (builtin bn σ ts) =
  builtin bn (lemma≤ bn) (eraseTel⋆ Γ (proj₁ (SIG bn)) ++ eraseTel ts)
erase (error A)         = error

eraseTel {As = []}     ts         = []
eraseTel {As = x ∷ As} (t ∷ tel) = erase t ∷ eraseTel tel
\end{code}
