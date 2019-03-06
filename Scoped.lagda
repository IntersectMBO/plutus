\begin{code}
module Scoped where
\end{code}

\begin{code}
open import Data.Nat
open import Data.Fin

open import Builtin.Constant.Type
open import Builtin
open import Raw
\end{code}

\begin{code}
data ScopedKind : Set where
  *   : ScopedKind
  _⇒_ : ScopedKind → ScopedKind → ScopedKind
  #   : ScopedKind

data ScopedTy : ℕ → Set where
  `   : ∀{n} → Fin n → ScopedTy n
  _⇒_ : ∀{n} → ScopedTy n → ScopedTy n → ScopedTy n
  Π   : ∀{n} → ScopedKind → ScopedTy (suc n) → ScopedTy n
  ƛ   : ∀{n} → ScopedKind → ScopedTy (suc n) → ScopedTy n
  _·_ : ∀{n} → ScopedTy n → ScopedTy n → ScopedTy n
  con : ∀{n} → TyCon → ScopedTy n
  size : ∀{n} → ℕ → ScopedTy n

data Weirdℕ : Set where
  Z : Weirdℕ
  S : Weirdℕ → Weirdℕ
  T : Weirdℕ → Weirdℕ

data WeirdFin : Weirdℕ → Set where
  Z : ∀{n} → WeirdFin (S n)
  S : ∀{n} → WeirdFin n → WeirdFin (S n)
  T : ∀{n} → WeirdFin n → WeirdFin (T n)
  
∥_∥ : Weirdℕ → ℕ
∥ Z   ∥ = zero
∥ S n ∥ = ∥ n ∥
∥ T n ∥ = suc ∥ n ∥

open import Data.Integer
open import Data.String

-- could index by size here, is there any point?
data SizedTermCon : Set where
  integer    : ∀ s
    → (i : ℤ)
    → BoundedI s i
    → SizedTermCon
  bytestring : ∀ s
    → (b : ByteString)
    → BoundedB s b
    → SizedTermCon
  size       : ℕ → SizedTermCon
  string     : String → SizedTermCon

data ScopedTm : Weirdℕ → Set where
  `    : ∀{n} → WeirdFin n → ScopedTm n 
  Λ    : ∀{n} → ScopedKind → ScopedTm (T n) → ScopedTm n
  _·⋆_ : ∀{n} → ScopedTm n → ScopedTy ∥ n ∥ → ScopedTm n
  ƛ    : ∀{n} → ScopedTy ∥ n ∥ → ScopedTm (S n) → ScopedTm n
  _·_  : ∀{n} → ScopedTm n → ScopedTm n → ScopedTm n
  con  : ∀{n} → SizedTermCon → ScopedTm n
  error : ∀{n} → ScopedTy ∥ n ∥ → ScopedTm n
  builtin : ∀{n} → Builtin → ScopedTm n

-- should just use ordinary kind for everything
deBruijnifyK : RawKind → ScopedKind
deBruijnifyK * = *
deBruijnifyK (K ⇒ J) = deBruijnifyK K ⇒ deBruijnifyK J
deBruijnifyK # = #

open import Data.Vec hiding (_>>=_; map)
open import Data.Maybe
open import Data.String
open import Relation.Nullary
open import Category.Monad
import Level
open RawMonad {f = Level.zero} monad

velemIndex : String → ∀{n} → Vec String n → Maybe (Fin n)
velemIndex x [] = nothing
velemIndex x (x' ∷ xs) with x Data.String.≟ x'
velemIndex x (x' ∷ xs) | yes p = just zero
velemIndex x (x' ∷ xs) | no ¬p = map Fin.suc (velemIndex x xs)

deBruijnifyTy : ∀{n} → Vec String n → RawTy → Maybe (ScopedTy n)
deBruijnifyTy g (` α) = map ` (velemIndex α g)
deBruijnifyTy g (A ⇒ B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A ⇒ B)
deBruijnifyTy g (Π x K B) =
  map (Π (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (ƛ x K B) =
  map (ƛ (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (A · B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A · B)
deBruijnifyTy g (con b)     = just (con b)
deBruijnifyTy g (size n)    = just (size n)

data WeirdVec (X : Set) : Weirdℕ → Set where
  nil : WeirdVec X Z
  consS : ∀{n} → X → WeirdVec X n → WeirdVec X (S n)
  consT : ∀{n} → X → WeirdVec X n → WeirdVec X (T n)

∥_∥Vec : ∀{X n} → WeirdVec X n → Vec X ∥ n ∥
∥ nil        ∥Vec = []
∥ consS x xs ∥Vec = ∥ xs ∥Vec
∥ consT x xs ∥Vec = x ∷ ∥ xs ∥Vec

velemIndexWeird : String → ∀{n} → WeirdVec String n → Maybe (WeirdFin n)
velemIndexWeird x nil = nothing
velemIndexWeird x (consS x' xs) with x Data.String.≟ x'
velemIndexWeird x (consS x' xs) | yes p = just Z
velemIndexWeird x (consS _  xs) | no ¬p = map S (velemIndexWeird x xs)
velemIndexWeird x (consT _  xs) = map T (velemIndexWeird x xs)

-- this could return a proof that that something is out of bounds
checkSize : RawTermCon → Maybe (SizedTermCon)
checkSize (integer s i) with boundedI? s i
checkSize (integer s i) | yes p    = just (integer s i p)
checkSize (integer s i) | no ¬p    = nothing
checkSize (bytestring s b) with boundedB? s b
checkSize (bytestring s b) | yes p = just (bytestring s b p)
checkSize (bytestring s b) | no ¬p = nothing
checkSize (size s)                 = just (size s)
checkSize (string x)               = just (string x)

deBruijnifyTm : ∀{n} → WeirdVec String n → RawTm → Maybe (ScopedTm n)
deBruijnifyTm g (` x) = map ` (velemIndexWeird x g)
deBruijnifyTm g (ƛ x A L) = do
  A ← deBruijnifyTy ∥ g ∥Vec A
  L ← deBruijnifyTm (consS x g) L
  return (ƛ A L)
deBruijnifyTm g (L · M) = do
  L ← deBruijnifyTm g L
  M ← deBruijnifyTm g M
  return (L · M)
deBruijnifyTm g (Λ x K L) =
  map (Λ (deBruijnifyK K)) (deBruijnifyTm (consT x g) L)
deBruijnifyTm g (L ·⋆ A) = do
  L ← deBruijnifyTm g L
  A ← deBruijnifyTy ∥ g ∥Vec A
  return (L ·⋆ A)
deBruijnifyTm g (con t) = map con (checkSize t)
deBruijnifyTm g (error A) = map error (deBruijnifyTy ∥ g ∥Vec A)
deBruijnifyTm g (builtin b) = just (builtin b) 

