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

open import Utils
open import Type
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic as A
open import Scoped
open import Builtin
import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) as T
import Builtin.Constant.Type ℕ ScopedTy as S

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
extricateTyConNf⋆ : ∀{Γ}(A : T.TyCon Γ) → S.TyCon (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateTyConNf⋆ T.integer = S.integer
extricateTyConNf⋆ T.bytestring = S.bytestring
extricateTyConNf⋆ T.string = S.string
extricateTyConNf⋆ T.unit = S.unit
extricateTyConNf⋆ T.bool = S.bool
extricateTyConNf⋆ (T.list A) = S.list (extricateNf⋆ A)
extricateTyConNf⋆ (T.pair A B) = S.pair (extricateNf⋆ A) (extricateNf⋆ B) 
extricateTyConNf⋆ T.Data = S.Data

extricateNf⋆ (Π {K = K} A) = Π K (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B) = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} A) = ƛ K (extricateNf⋆ A)
extricateNf⋆ (ne n) = extricateNe⋆ n
extricateNf⋆ (con c) = con (extricateTyConNf⋆ c)
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

extricateC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → Utils.TermCon
extricateC (integer i)    = integer i
extricateC (bytestring b) = bytestring b
extricateC (string s)     = string s
extricateC (bool b)       = bool b
extricateC unit           = unit
extricateC (Data d)       = Data d

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

lemma⋆ : ∀ b → len⋆ (proj₁ (ISIG b)) ≡ arity⋆ b
lemma⋆ addInteger = refl
lemma⋆ subtractInteger = refl
lemma⋆ multiplyInteger = refl
lemma⋆ divideInteger = refl
lemma⋆ quotientInteger = refl
lemma⋆ remainderInteger = refl
lemma⋆ modInteger = refl
lemma⋆ lessThanInteger = refl
lemma⋆ lessThanEqualsInteger = refl
lemma⋆ equalsInteger = refl
lemma⋆ appendByteString = refl
lemma⋆ lessThanByteString = refl
lemma⋆ lessThanEqualsByteString = refl
lemma⋆ sha2-256 = refl
lemma⋆ sha3-256 = refl
lemma⋆ verifySignature = refl
lemma⋆ equalsByteString = refl
lemma⋆ ifThenElse = refl
lemma⋆ appendString = refl
lemma⋆ trace = refl
lemma⋆ equalsString = refl
lemma⋆ encodeUtf8 = refl
lemma⋆ decodeUtf8 = refl
lemma⋆ fstPair = refl
lemma⋆ sndPair = refl
lemma⋆ nullList = refl
lemma⋆ headList = refl
lemma⋆ tailList = refl
lemma⋆ chooseList = refl
lemma⋆ constrData = refl
lemma⋆ mapData = refl
lemma⋆ listData = refl
lemma⋆ iData = refl
lemma⋆ bData = refl
lemma⋆ unConstrData = refl
lemma⋆ unMapData = refl
lemma⋆ unListData = refl
lemma⋆ unIData = refl
lemma⋆ unBData = refl
lemma⋆ equalsData = refl
lemma⋆ chooseData = refl
lemma⋆ chooseUnit = refl
lemma⋆ mkPairData = refl
lemma⋆ mkNilData = refl
lemma⋆ mkNilPairData = refl
lemma⋆ mkCons = refl
lemma⋆ consByteString = refl
lemma⋆ sliceByteString = refl
lemma⋆ lengthOfByteString = refl
lemma⋆ indexByteString = refl
lemma⋆ blake2b-256 = refl

lemma : ∀ b → wtoℕTm (len (proj₁ (proj₂ (ISIG b)))) ≡ Scoped.arity b
lemma addInteger = refl
lemma subtractInteger = refl
lemma multiplyInteger = refl
lemma divideInteger = refl
lemma quotientInteger = refl
lemma remainderInteger = refl
lemma modInteger = refl
lemma lessThanInteger = refl
lemma lessThanEqualsInteger = refl
lemma equalsInteger = refl
lemma appendByteString = refl
lemma lessThanByteString = refl
lemma lessThanEqualsByteString = refl
lemma sha2-256 = refl
lemma sha3-256 = refl
lemma verifySignature = refl
lemma equalsByteString = refl
lemma ifThenElse = refl
lemma appendString = refl
lemma trace = refl
lemma equalsString = refl
lemma encodeUtf8 = refl
lemma decodeUtf8 = refl
lemma fstPair = refl
lemma sndPair = refl
lemma nullList = refl
lemma headList = refl
lemma tailList = refl
lemma chooseList = refl
lemma constrData = refl
lemma mapData = refl
lemma listData = refl
lemma iData = refl
lemma bData = refl
lemma unConstrData = refl
lemma unMapData = refl
lemma unListData = refl
lemma unIData = refl
lemma unBData = refl
lemma equalsData = refl
lemma chooseData = refl
lemma chooseUnit = refl
lemma mkPairData = refl
lemma mkNilData = refl
lemma mkNilPairData = refl
lemma mkCons = refl
lemma consByteString = refl
lemma sliceByteString = refl
lemma lengthOfByteString = refl
lemma indexByteString = refl
lemma blake2b-256 = refl

≡2≤‴ : ∀{m n} → m ≡ n → m ≤‴ n
≡2≤‴ refl = ≤‴-refl

extricate : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → ScopedTm (len Γ)
extricate (` x) = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} t) = ƛ (extricateNf⋆ A) (extricate t)
extricate (t · u) = extricate t · extricate u
extricate (Λ {K = K} t) = Λ K (extricate t)
extricate {Φ}{Γ} (_·⋆_ t A) = extricate t ScopedTm.·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg)
  (extricate t)
extricate (unwrap t) = unwrap (extricate t)
extricate (con c) = con (extricateC c)
extricate (ibuiltin b) = ibuiltin b
extricate {Φ}{Γ} (error A) = error (extricateNf⋆ A)
\end{code}
