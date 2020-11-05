\begin{code}
module Scoped.Extrication where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.Vec
open import Function using (_∘_)
open import Data.Sum using (inj₁;inj₂)
open import Data.Product renaming (_,_ to _,,_)

open import Type
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic as A
open import Scoped
open import Builtin
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con 
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as B
open import Type.BetaNormal
open import Type.RenamingSubstitution as T
\end{code}

type level

\begin{code}
len⋆ : Ctx⋆ → ℕ
len⋆ ∅ = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

extricateVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
extricateVar⋆ Z     = zero
extricateVar⋆ (S α) = suc (extricateVar⋆ α)

extricateNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
extricateNe⋆ : ∀{Γ K}(A : Γ ⊢Ne⋆ K) → ScopedTy (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateNf⋆ (Π {K = K} A) = Π K (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B) = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} A) = ƛ K (extricateNf⋆ A)
extricateNf⋆ (ne n) = extricateNe⋆ n
extricateNf⋆ (con c) = con c
extricateNf⋆ (μ A B) = μ (extricateNf⋆ A) (extricateNf⋆ B)

extricateNe⋆ (` α) = ` (extricateVar⋆ α)
extricateNe⋆ (n · n') = extricateNe⋆ n · extricateNf⋆ n'
\end{code}


\begin{code}
len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

open import Relation.Binary.PropositionalEquality as Eq

extricateVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → WeirdFin (len Γ)
extricateVar Z = Z
extricateVar (S x) = S (extricateVar x)
extricateVar (T x) = T (extricateVar x)

extricateC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → Scoped.TermCon
extricateC (integer i)    = integer i
extricateC (bytestring b) = bytestring b
extricateC (string s)     = string s
extricateC (bool b)       = bool b
extricateC (char c)       = char c
extricateC unit           = unit

open import Data.Product as P
open import Function hiding (_∋_)

extricateSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → Scoped.Tel⋆ (len⋆ Γ) (len⋆ Δ)
extricateSub {Δ = ∅}     σ = []
extricateSub {Γ}{Δ ,⋆ K} σ =
  Eq.subst (Scoped.Tel⋆ (len⋆ Γ))
           (+-comm (len⋆ Δ) 1)
           (extricateSub {Δ = Δ} (σ ∘ S) ++ Data.Vec.[ extricateNf⋆ (σ Z) ]) 

open import Data.List

lemma⋆ : ∀ b → len⋆ (proj₁ (SIG b)) ≡ arity⋆ b
lemma⋆ addInteger = refl
lemma⋆ subtractInteger = refl
lemma⋆ multiplyInteger = refl
lemma⋆ divideInteger = refl
lemma⋆ quotientInteger = refl
lemma⋆ remainderInteger = refl
lemma⋆ modInteger = refl
lemma⋆ lessThanInteger = refl
lemma⋆ lessThanEqualsInteger = refl
lemma⋆ greaterThanInteger = refl
lemma⋆ greaterThanEqualsInteger = refl
lemma⋆ equalsInteger = refl
lemma⋆ concatenate = refl
lemma⋆ takeByteString = refl
lemma⋆ dropByteString = refl
lemma⋆ sha2-256 = refl
lemma⋆ sha3-256 = refl
lemma⋆ verifySignature = refl
lemma⋆ equalsByteString = refl
lemma⋆ ifThenElse = refl

lemma : ∀ b → Data.List.length (proj₁ (proj₂ (SIG b))) ≡ arity b
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

≡2≤‴ : ∀{m n} → m ≡ n → m ≤‴ n
≡2≤‴ refl = ≤‴-refl

extricateTel : ∀ {Φ Γ Δ}(σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)(As : List (Δ ⊢Nf⋆ *))
  → A.Tel Γ Δ σ As
  → Vec (ScopedTm (len Γ)) (Data.List.length As)

extricate : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → ScopedTm (len Γ)

extricateTel σ [] x = []
extricateTel σ (A ∷ As) (t ∷ ts) = extricate t ∷ extricateTel σ As ts

extricate (` x) = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} t) = ƛ (extricateNf⋆ A) (extricate t)
extricate (t · u) = extricate t · extricate u
extricate (Λ {K = K} t) = Λ K (extricate t)
extricate {Φ}{Γ} (_·⋆_ t A) = extricate t ScopedTm.·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg)
  (extricate t)
extricate (unwrap t) = unwrap (extricate t)
extricate (con c) = con (extricateC c)
extricate {Φ}{Γ} (builtin b σ ts) =
  builtin
    b
    (inj₂ ((lemma⋆ b) ,, (≡2≤‴ (lemma b))))
    (extricateSub σ)
    (extricateTel σ _ ts)
extricate (pbuiltin b Ψ' σ As' p x) = error (extricateNf⋆ (abstract3' _ _ Ψ' _ As' p (proj₂ (proj₂ (SIG b))) σ))
extricate (ibuiltin b σ⋆ σ) = error (extricateNf⋆ (substNf σ⋆ (proj₂ (proj₂ (ISIG b)))))
extricate (ipbuiltin b Ψ' Δ' p σ⋆ σ) = error (extricateNf⋆ (apply⋆ _ _ _ Ψ' _ Δ' p (proj₂ (proj₂ (ISIG b))) σ⋆ σ))
extricate {Φ}{Γ} (error A) = error (extricateNf⋆ A)
\end{code}
