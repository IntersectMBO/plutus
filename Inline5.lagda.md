Inline translation
Philip Wadler, Ramsay Taylor, Jacco Krijnen, Roman Kireev, Ziyang Liu
30 Dec 2025

Uses a `check` procedure rather than a decision procedure.

Updated to use a relationship between two stacks, with the two stacks
themselves left implicit.

# Imports

```
{-# OPTIONS --exact-split --rewriting #-}
module Inline5 where
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just; _>>=_; _<∣>_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to infixl 5 _,_)
open import Data.Product.Properties using (,-injectiveˡ; ,-injectiveʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; _≢_; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; step-≡-⟨; _∎)
```

# Precedence

```
infix   4  _∋_ _⊇_ _⊢_ _⊒_ _⊢_↝_ _≽_
infixl  5  _,_
infix   6  ƛ_ ƛ□_ ƛ↓_
infixl  7  _·_
infix   7  _·↓
infixr  7  _⇒_
infix   8  `_ `↓_
infix   9  S_
infixl 10  _∘_ _∘ʳ_
infix  10  _↑ _↑_ _↑ᶻ _↑ˢ _↑ʳ [_]_ [_]ʳ_ _[_]
```

Natural number literals
```
instance
  NumNat : Number ℕ
  NumNat .Number.Constraint _ = ⊤
  NumNat .Number.fromNat    m = m

variable
  k l m n : ℕ

_ : ℕ
_ = 42
```

Syntax
```
data Type : Set where
  `ℕ   : Type
  _⇒_  : Type → Type → Type

variable
  A B C A′ B′ C′ : Type

data Env : Set where
  ∅   : Env
  _,_ : Env → Type → Env

variable
  Γ Δ Θ : Env

data _∋_ : Env → Type → Set where
  Z   :   Γ , A ∋ A
  S_  :   Γ ∋ B
          ---------
        → Γ , A ∋ B

variable
  x y : Γ ∋ A

data _⊢_ : Env → Type → Set where

  `_ :
      (x : Γ ∋ A)
    → -----------
      Γ ⊢ A

  ƛ_ :
      (N : Γ , A ⊢ B)
    → ---------------
      Γ ⊢ A ⇒ B

  _·_ :
      (L : Γ ⊢ A ⇒ B)
      (M : Γ ⊢ A)
    → -----------
      Γ ⊢ B

variable
  L M N L′ M′ N′ : Γ ⊢ A
```

Convert naturals to variables, using type classes
```
record Convert (n : ℕ) (X : Set) : Set where
  field
    convert : X

open Convert {{...}}

instance
  zero∋ : Convert zero (Γ , A ∋ A)
  zero∋ .Convert.convert = Z

instance
  suc∋ : {{Convert n (Γ ∋ B)}} → Convert (suc n) (Γ , A ∋ B)
  suc∋ .Convert.convert = S convert

instance
  Num∋ : Number (Γ ∋ A)
  Num∋ .Number.Constraint n = Convert n (_ ∋ _)
  Num∋ .Number.fromNat n = convert

_ : Γ , A , B ∋ A
_ = 1
```

Semantics
```
⟦_⟧ᵗ : Type → Set
⟦ `ℕ ⟧ᵗ     =  ℕ
⟦ A ⇒ B ⟧ᵗ  =  ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ

⟦_⟧ᵉ : Env → Set
⟦ ∅ ⟧ᵉ      =  ⊤
⟦ Γ , A ⟧ᵉ  =  ⟦ Γ ⟧ᵉ × ⟦ A ⟧ᵗ

variable
  η : ⟦ Γ ⟧ᵉ

⟦_⟧ᵛ : Γ ∋ A → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
⟦ Z ⟧ᵛ    (η , v)  =  v
⟦ S x ⟧ᵛ  (η , v)  =  ⟦ x ⟧ᵛ η

⟦_⟧ : Γ ⊢ A → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ
⟦ ` x ⟧    η  =  (⟦ x ⟧ᵛ η)
⟦ ƛ N ⟧    η  =  (λ v → ⟦ N ⟧ (η , v))
⟦ L · M ⟧  η  =  ⟦ L ⟧ η (⟦ M ⟧ η)
```

Example: Church numerals
```
Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ (A ⇒ A)

twoᶜ : Γ ⊢ Ch A
twoᶜ = ƛ ƛ (` 1 · (` 1 · ` 0))

plusᶜ : Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (` 3 · ` 1 · (` 2 · ` 1 · ` 0))

_ : ⟦ plusᶜ {A = A} · twoᶜ · twoᶜ ⟧ tt ≡ λ s z → s (s (s (s z)))
_ = refl
```


# Renaming

The development of renaming and of substitution is quite similar.
Standard forms ``ρ ↑ʳ ▷ʳ 0`` and ``σ ↑ˢ ▷ ` 0`` are used when pushing
underneath a lambda.

```
data _⊇_ : Env → Env → Set where

  ∅ :
      -----
      Δ ⊇ ∅

  _,_ :
      (ρ : Δ ⊇ Γ)
      (x : Δ ∋ A)
    → -----------
      Δ ⊇ Γ , A

variable
  ρ υ : Δ ⊇ Γ

_↑ʳ :
    (ρ : Δ ⊇ Γ)
  → ---------
    Δ , A ⊇ Γ
∅ ↑ʳ        =  ∅
(ρ , x) ↑ʳ  =  ρ ↑ʳ , S x

lookupʳ :
    (ρ : Δ ⊇ Γ)
    (x : Γ ∋ A)
  → -----------
    Δ ∋ A
lookupʳ (ρ , x) Z      =  x
lookupʳ (ρ , x) (S y)  =  lookupʳ ρ y

[_]ʳ_ :
    (ρ : Δ ⊇ Γ)
    (M : Γ ⊢ A)
  → -----------
    Δ ⊢ A
[ ρ ]ʳ (` x)    =  ` (lookupʳ ρ x)
[ ρ ]ʳ (ƛ N)    =  ƛ ([ ρ ↑ʳ , 0 ]ʳ N)
[ ρ ]ʳ (L · M)  =  [ ρ ]ʳ L · [ ρ ]ʳ M
```


# Identity and composition
```
idʳ :
    -----
    Γ ⊇ Γ
idʳ {Γ = ∅}      =  ∅
idʳ {Γ = Γ , A}  =  idʳ ↑ʳ , 0

_∘ʳ_ :
    (ρ : Δ ⊇ Θ)
    (υ : Θ ⊇ Γ)
  → ------------
     Δ ⊇ Γ
ρ ∘ʳ ∅ = ∅
ρ ∘ʳ (υ , x) = ρ ∘ʳ υ , lookupʳ ρ x
```


# Weakening, and weakening with explicit type
```
_↑ :
     (M : Γ ⊢ B)
   → -----------
     Γ , A ⊢ B
M ↑   =  [ idʳ ↑ʳ ]ʳ M

_↑_ :
     (M : Γ ⊢ B)
     (A : Type)
   → -----------
     Γ , A ⊢ B
M ↑ A  =  M ↑
```


# Substitution
```
data _⊒_ : Env → Env → Set where

  ∅ :
      -----
      Δ ⊒ ∅

  _,_ :
      (σ : Δ ⊒ Γ)
      (M : Δ ⊢ A)
    → -----------
       Δ ⊒ Γ , A

variable
  σ τ : Δ ⊒ Γ

_↑ˢ :
    (σ : Δ ⊒ Γ)
  → ---------
    Δ , A ⊒ Γ
∅ ↑ˢ = ∅
(σ , M) ↑ˢ = σ ↑ˢ , M ↑

lookup :
    (σ : Δ ⊒ Γ)
    (x : Γ ∋ A)
  → -----------
    Δ ⊢ A
lookup (σ , M) Z      =  M
lookup (σ , M) (S x)  =  lookup σ x

[_]_ :
    (σ : Δ ⊒ Γ)
    (M : Γ ⊢ A)
  → -----------
     Δ ⊢ A
[ σ ] (` x)    =  lookup σ x
[ σ ] (ƛ N)    =  ƛ ([ σ ↑ˢ , ` 0 ] N)
[ σ ] (L · M)  =  [ σ ] L · [ σ ] M
```

# Identity and composition
```
id :
    -----
    Γ ⊒ Γ
id {Γ = ∅}      =  ∅
id {Γ = Γ , A}  =  id ↑ˢ , ` 0

_∘_ :
    (σ : Δ ⊒ Θ)
    (τ : Θ ⊒ Γ)
  → ------------
     Δ ⊒ Γ
σ ∘ ∅ = ∅
σ ∘ (τ , M) = σ ∘ τ , [ σ ] M
```


# Zippers
```
data _⊢_↝_ : Env → Type → Type → Set where

  □ :
      ---------
      Γ ⊢ A ↝ A

  _·_ :
      (z : Γ ⊢ B ↝ C)
      (M : Γ ⊢ A)
    → ---------------
      Γ ⊢ (A ⇒ B) ↝ C

variable
  z z′ : Γ ⊢ A ↝ B

pattern _·[_]_ L A M = _·_ {A = A} L M

_[_] :
    (z : Γ ⊢ A ↝ B)
    (L : Γ ⊢ A)
  → ---------------
    Γ ⊢ B
□        [ L ]  =  L
(z · M)  [ L ]  =  z [ L · M ]

_↑ᶻ : Γ ⊢ A ↝ B → Γ , C ⊢ A ↝ B
□ ↑ᶻ        =  □
(z · M) ↑ᶻ  =  (z ↑ᶻ) · (M ↑)

_↑ᶻ_ : Γ ⊢ A ↝ B → (C : Type) → Γ , C ⊢ A ↝ B
z ↑ᶻ C  =  z ↑ᶻ
```

# Relating two zippers
```
data _≽_ : (z : Γ ⊢ A ↝ B) (z′ : Γ ⊢ A′ ↝ B) → Set where

  □ :
      ------------------------
      _≽_ {Γ = Γ} {A = A} □ □

  keep :
      {z : Γ ⊢ B ↝ C}
      (M : Γ ⊢ A)
      (zz : z ≽ z′)
    → ---------------------
      (z · M) ≽ (z′ · M)

  drop :
      {z : Γ ⊢ B ↝ C}
      (M : Γ ⊢ A)
      (zz : z ≽ z′)
    → -------------
      (z · M) ≽ z′

variable
  zz : z ≽ z′

_↑ᶻᶻ : z ≽ z′ → (z ↑ᶻ C) ≽ (z′ ↑ᶻ C)
_↑ᶻᶻ □ = □
_↑ᶻᶻ (keep M zᵃ) = keep (M ↑) (zᵃ ↑ᶻᶻ)
_↑ᶻᶻ (drop M zᵃ) = drop (M ↑) (zᵃ ↑ᶻᶻ)

idᶻᶻ : (z : Γ ⊢ A ↝ B) → z ≽ z
idᶻᶻ □ = □
idᶻᶻ (z · M) = keep M (idᶻᶻ z)
```

# Inline relation

Note the construct ``σ ↑ˢ ▷ M ↑`` in the lambda rule is similar to the
construct ``σ ↑ˢ ▷ ` 0`` used when passing underneath a lambda in
substitution.

```
data Inline : (σ : Γ ⊒ Γ)
              {z : Γ ⊢ A ↝ B} {z′ : Γ ⊢ A′ ↝ B} (zz : z ≽ z′)
              (M : Γ ⊢ A) (M′ : Γ ⊢ A′)
              → Set where

  `_ :
      (x : Γ ∋ A)
    → -----------------------------
      Inline σ (idᶻᶻ z) (` x) (` x)

  `↓_ :
      (r : Inline σ zz (lookup σ x) M′)
    → ---------------------------------
      Inline σ zz (` x) M′

  ƛ□_ :
      (t : Inline (σ ↑ˢ , ` 0) □ N N′)
    → --------------------------------
      Inline σ □ (ƛ N) (ƛ N′)

  ƛ_ :
      (t : Inline (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N N′)
    → ---------------------------------------
      Inline σ (keep M zz) (ƛ N) (ƛ N′)

  ƛ↓_ :
      (t : Inline (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N (N′ ↑))
    → -------------------------------------------
      Inline σ (drop M zz) (ƛ N) N′

  _·_ :
      (r : Inline σ (keep M zz) L L′)
      (s : Inline σ □ M M′)
    → -------------------------------
      Inline σ zz (L · M) (L′ · M′)

  _·↓ :
      (r : Inline σ (drop M zz) L N′)
    → -------------------------------
      Inline σ zz (L · M) N′

data Inline⁺ : (∅ ⊢ A) → (∅ ⊢ A) → Set where
  _↑ᵗ :
      (r : Inline ∅ □ M M′)
    → ---------------------
      Inline⁺ M M′

  _⨾_ :
      (r : Inline⁺ M N)
      (s : Inline⁺ N M′)
    → ------------------
      Inline⁺ M M′
```

# Examples

```
A₀ : Type
A₀ = `ℕ

M₀ : ∅ ⊢ A₀ ⇒ A₀
M₀ = ƛ (` 0)

_ : Inline ∅ □ M₀ M₀
_ = ƛ□ (` 0)

_ : Inline ∅ □ M₀ M₀
_ = ƛ□ (`↓ (` 0))

M₁ : ∅ ⊢ (A₀ ⇒ A₀) ⇒ (A₀ ⇒ A₀)
M₁ = ƛ (` 0)

M₂ : ∅ ⊢ A₀ ⇒ A₀
M₂ = M₁ · M₀

_ : Inline ∅ □ M₂ M₀
_ = ((ƛ↓ (`↓ (ƛ□ (` 0)))) ·↓)

M₃ M₄ M₅ : ∅ ⊢ (A₀ ⇒ A₀ ⇒ A₀) ⇒ A₀ ⇒ A₀
-- M₃ = λg.λx.((λy.g y y) x)
-- M₄ = λg.λx.(g x x)
-- M₅ = λg.λx.((λy.g x y) x)
M₃ = ƛ (ƛ ((ƛ (` 2 · ` 0 · ` 0)) · ` 0))
M₄ = ƛ (ƛ (` 1 · ` 0 · ` 0))
M₅ = ƛ (ƛ ((ƛ (` 2 · ` 1 · ` 0)) · ` 0))

_ : Inline ∅ □ M₃ M₄
_ = (ƛ□ (ƛ□ (ƛ↓ (` 2 · `↓ (` 1) · `↓ (` 1))) ·↓))

_ : Inline ∅ □ M₃ M₅
_ = (ƛ□ (ƛ□ ((ƛ ` 2 · `↓ (` 1) · ` 0) · ` 0)))
```


# Application and extensionality
```
variable
  X Y : Set

_$_ : (X → Y) → X → Y
f $ x  =  f x

postulate
  extensionality : ∀ {f g : X → Y} → (∀ (x : X) → f x ≡ g x) → f ≡ g
```

# Semantics of renaming
```
⟦_⟧ʳ : Δ ⊇ Γ → ⟦ Δ ⟧ᵉ → ⟦ Γ ⟧ᵉ
⟦ ∅ ⟧ʳ η      =  tt
⟦ ρ , x ⟧ʳ η  =  (⟦ ρ ⟧ʳ η) , (⟦ x ⟧ᵛ η)

weakenʳ : ∀ (ρ : Δ ⊇ Γ) (η : ⟦ Δ ⟧ᵉ) (v : ⟦ A ⟧ᵗ) →
  ⟦ ρ ↑ʳ ⟧ʳ (η , v) ≡ ⟦ ρ ⟧ʳ η
weakenʳ ∅        η v  =  refl
weakenʳ (ρ , x)  η v  =  cong₂ _,_ (weakenʳ ρ η v) refl

renameᵛ : ∀ (ρ : Δ ⊇ Γ) (x : Γ ∋ A) (η : ⟦ Δ ⟧ᵉ) →
  ⟦ lookupʳ ρ x ⟧ᵛ η ≡ ⟦ x ⟧ᵛ (⟦ ρ ⟧ʳ η)
renameᵛ (ρ , y)  Z      η  =  refl
renameᵛ (ρ , y)  (S x)  η  =  renameᵛ ρ x η

rename : ∀ (ρ : Δ ⊇ Γ) (M : Γ ⊢ A) (η : ⟦ Δ ⟧ᵉ) →
  ⟦ [ ρ ]ʳ M ⟧ η ≡ ⟦ M ⟧ (⟦ ρ ⟧ʳ η)
rename ρ (` x) η  =  renameᵛ ρ x η
rename ρ (ƛ N) η
  =  extensionality (λ v →
       begin
         ⟦ [ ρ ↑ʳ , 0 ]ʳ N ⟧ (η , v)
       ≡⟨ rename (ρ ↑ʳ , 0) N (η , v) ⟩
         ⟦ N ⟧ (⟦ ρ ↑ʳ , 0 ⟧ʳ (η , v))
       ≡⟨⟩
         ⟦ N ⟧ (⟦ ρ ↑ʳ ⟧ʳ (η , v) , ⟦ 0 ⟧ᵛ (η , v))
       ≡⟨ cong ⟦ N ⟧ (cong₂ _,_ (weakenʳ ρ η v) refl) ⟩
         ⟦ N ⟧ (⟦ ρ ⟧ʳ η , v)
       ∎)
rename ρ (L · M) η
  =  cong₂ _$_ (rename ρ L η) (rename ρ M η)

identityʳ : ∀ (η : ⟦ Γ ⟧ᵉ) → ⟦ idʳ ⟧ʳ η ≡ η
identityʳ {Γ = ∅}      tt       =  refl
identityʳ {Γ = Γ , A}  (η , v)
  =  begin
       ⟦ idʳ ↑ʳ , 0 ⟧ʳ (η , v)
     ≡⟨⟩
       ⟦ idʳ ↑ʳ ⟧ʳ (η , v) , ⟦ 0 ⟧ᵛ (η , v)
     ≡⟨ cong₂ _,_ (weakenʳ idʳ η v) refl ⟩
       ⟦ idʳ ⟧ʳ η , v
     ≡⟨ cong₂ _,_ (identityʳ η) refl ⟩
       η , v
     ∎
```

# Semantics of weakening

Weakening drops the last value in the evaluation environment.
```
weaken : ∀ (M : Γ ⊢ A) (η : ⟦ Γ ⟧ᵉ) (v : ⟦ B ⟧ᵗ)
  → ⟦ M ↑ ⟧ (η , v) ≡ ⟦ M ⟧ η
weaken M η v
  = begin
      ⟦ [ idʳ ↑ʳ ]ʳ M ⟧ (η , v)
    ≡⟨ rename (idʳ ↑ʳ) M (η , v) ⟩
      ⟦ M ⟧ (⟦ idʳ ↑ʳ ⟧ʳ (η , v))
    ≡⟨ cong ⟦ M ⟧ (weakenʳ idʳ η v) ⟩
      ⟦ M ⟧ (⟦ idʳ ⟧ʳ η)
    ≡⟨ cong ⟦ M ⟧ (identityʳ η) ⟩
      ⟦ M ⟧ η
    ∎
```

# Semantics of substitution
```
⟦_⟧ˢ : Δ ⊒ Γ → ⟦ Δ ⟧ᵉ → ⟦ Γ ⟧ᵉ
⟦ ∅ ⟧ˢ η      =  tt
⟦ σ , M ⟧ˢ η  =  ⟦ σ ⟧ˢ η , ⟦ M ⟧ η

weakenˢ : ∀ (σ : Δ ⊒ Γ) (η : ⟦ Δ ⟧ᵉ) (v : ⟦ A ⟧ᵗ) →
  ⟦ σ ↑ˢ ⟧ˢ (η , v) ≡ ⟦ σ ⟧ˢ η
weakenˢ ∅        η v  =  refl
weakenˢ (σ , M)  η v  =  cong₂ _,_ (weakenˢ σ η v) (weaken M η v)
```

The semantics of applying a substitution to a term is composition
of the semantics of the term with the semantics of the substitution.
```
substitutionᵛ : ∀ (σ : Δ ⊒ Γ) (x : Γ ∋ A) (η : ⟦ Δ ⟧ᵉ) →
  ⟦ lookup σ x ⟧ η ≡ ⟦ x ⟧ᵛ (⟦ σ ⟧ˢ η)
substitutionᵛ (σ , M) Z η      =  refl
substitutionᵛ (σ , M) (S x) η  =  substitutionᵛ σ x η

substitution : ∀ (σ : Δ ⊒ Γ) (M : Γ ⊢ A) (η : ⟦ Δ ⟧ᵉ) →
  ⟦ [ σ ] M ⟧ η ≡ ⟦ M ⟧ (⟦ σ ⟧ˢ η)
substitution σ (` x) η
  =  substitutionᵛ σ x η
substitution σ (ƛ N) η
  =  extensionality (λ v →
       begin
         ⟦ [ σ ↑ˢ , ` 0 ] N ⟧ (η , v)
       ≡⟨ substitution (σ ↑ˢ , ` 0) N (η , v) ⟩
         ⟦ N ⟧ (⟦ σ ↑ˢ , ` 0 ⟧ˢ (η , v))
       ≡⟨⟩
         ⟦ N ⟧ (⟦ σ ↑ˢ ⟧ˢ (η , v) , ⟦ ` 0 ⟧ (η , v))
       ≡⟨ cong ⟦ N ⟧ (cong₂ _,_ (weakenˢ σ η v) refl) ⟩
         ⟦ N ⟧ (⟦ σ ⟧ˢ η , v)
       ∎)
substitution σ (L · M) η
  =  cong₂ _$_ (substitution σ L η) (substitution σ M η)

identity : ∀ (η : ⟦ Γ ⟧ᵉ) → ⟦ id ⟧ˢ η ≡ η
identity {Γ = ∅}      tt       =  refl
identity {Γ = Γ , A}  (η , v)
  =  begin
       ⟦ id ↑ˢ , ` 0 ⟧ˢ (η , v)
     ≡⟨⟩
       ⟦ id ↑ˢ ⟧ˢ (η , v) , ⟦ ` 0 ⟧ (η , v)
     ≡⟨ cong₂ _,_ (weakenˢ id η v) refl ⟩
       ⟦ id ⟧ˢ η , v
     ≡⟨ cong₂ _,_ (identity η) refl ⟩
       η , v
     ∎
```

# Semantics of zip

```
⟦_⟧ᶻ : (Γ ⊢ A ↝ B) → ⟦ Γ ⟧ᵉ → ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
⟦ □ ⟧ᶻ      η w  =  w
⟦ z · M ⟧ᶻ  η w  =  ⟦ z ⟧ᶻ η  (w (⟦ M ⟧ η))

zipper : (z : Γ ⊢ A ↝ B) (L : Γ ⊢ A) (η : ⟦ Γ ⟧ᵉ) →
  ⟦ z [ L ] ⟧ η ≡ ⟦ z ⟧ᶻ η (⟦ L ⟧ η)
zipper □ L η = refl
zipper (z · M) L η =
  begin
    ⟦ (z · M) [ L ] ⟧ η
  ≡⟨⟩ -- def'n `(z · M) [ L ]`
    ⟦ z [ L · M ] ⟧ η
  ≡⟨ zipper z (L · M) η ⟩
    ⟦ z ⟧ᶻ η (⟦ L · M ⟧ η)
  ≡⟨⟩ -- def'n `⟦ L · M ⟧`
    ⟦ z ⟧ᶻ η (⟦ L ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩ -- def'n `⟦ z · M ⟧ᶻ`
    ⟦ z · M ⟧ᶻ η (⟦ L ⟧ η)
  ∎

weakenᶻ : (z : Γ ⊢ A ↝ B) (η : ⟦ Γ ⟧ᵉ) (v : ⟦ C ⟧ᵗ) →
  ⟦ z ↑ᶻ ⟧ᶻ (η , v) ≡ ⟦ z ⟧ᶻ η
weakenᶻ □ η v = refl
weakenᶻ (z · M) η v = extensionality (λ w →
  begin
    ⟦ (z · M) ↑ᶻ ⟧ᶻ (η , v) w
  ≡⟨⟩  -- def'n `⟦ z ↑ᶻ · M ↑ ⟧ᶻ (η , v) w`
    ⟦ z ↑ᶻ ⟧ᶻ (η , v) (w (⟦ M ↑ ⟧ (η , v)))
  ≡⟨ cong₂ _$_ (weakenᶻ z η v) (cong w (weaken M η v)) ⟩
    ⟦ z ⟧ᶻ η (w (⟦ M ⟧ η))
  ≡⟨⟩  -- def'n `⟦ z · M ⟧ᶻ η w`
    ⟦ z · M ⟧ᶻ η w
  ∎)
```

# Lemmas about zip

```
zip : ∀ (z : Γ ⊢ A ↝ B) (N N′ : Γ ⊢ A) (η : ⟦ Γ ⟧ᵉ)
  → ⟦ N ⟧ η ≡ ⟦ N′ ⟧ η
    --------------------------------
  → ⟦ z [ N ] ⟧ η ≡ ⟦ z [ N′ ] ⟧ η
zip z N N′ η e =
  begin
    ⟦ z [ N ] ⟧ η
  ≡⟨ zipper z N η ⟩
    ⟦ z ⟧ᶻ η (⟦ N ⟧ η)
  ≡⟨ cong (⟦ z ⟧ᶻ η) e ⟩
    ⟦ z ⟧ᶻ η (⟦ N′ ⟧ η)
  ≡⟨ zipper z N′ η ⟨
    ⟦ z [ N′ ] ⟧ η
  ∎

zip↑ : ∀ (z : Γ ⊢ B ↝ C) (N : Γ ⊢ B) (N′ : Γ , A ⊢ B) (η : ⟦ Γ ⟧ᵉ) (v : ⟦ A ⟧ᵗ)
  → ⟦ N ⟧ η ≡ ⟦ N′ ⟧ (η , v)
    --------------------------------------------
  → ⟦ z [ N ] ⟧ η ≡ ⟦ (z ↑ᶻ) [ N′ ] ⟧ (η , v)
zip↑ z N N′ η v e =
  begin
    ⟦ z [ N ] ⟧ η
  ≡⟨ zipper z N η ⟩
    ⟦ z ⟧ᶻ η (⟦ N ⟧ η)
  ≡⟨ cong₂ _$_ (sym (weakenᶻ z η v)) e ⟩
   ⟦ z ↑ᶻ ⟧ᶻ (η , v) (⟦ N′ ⟧ (η , v))
  ≡⟨ zipper (z ↑ᶻ) N′ (η , v) ⟨
    ⟦ (z ↑ᶻ) [ N′ ] ⟧ (η , v)
  ∎
```

# Lookup lemma

If `σ` preserves `η`, then `lookup σ x` and `x` are identical under `η`
```
lookup-lemma :
  ∀ (x : Γ ∋ A)
  → (σ : Γ ⊒ Γ)
  → (η : ⟦ Γ ⟧ᵉ)
  → η ≡ ⟦ σ ⟧ˢ η
  → ⟦ ` x ⟧ η ≡ ⟦ lookup σ x ⟧ η
lookup-lemma Z (σ , M) (η , v) e
  =  ,-injectiveʳ e
lookup-lemma (S x) (σ , M) (η , v) e
  =  begin
       ⟦ ` (S x) ⟧ (η , v)
     ≡⟨⟩
       ⟦ x ⟧ᵛ η
     ≡⟨ cong ⟦ x ⟧ᵛ (,-injectiveˡ e) ⟩
       ⟦ x ⟧ᵛ (⟦ σ ⟧ˢ (η , v))
     ≡⟨ substitutionᵛ σ x (η , v) ⟨
       ⟦ lookup σ x ⟧ (η , v)
     ≡⟨⟩
       ⟦ lookup (σ , M) (S x) ⟧ (η , v)
     ∎
```

# ƛ-lemmas
```
promote : ∀ (σ : Γ ⊒ Γ) (η : ⟦ Γ ⟧ᵉ) (v : ⟦ A ⟧ᵗ)
  → η ≡ ⟦ σ ⟧ˢ η
  → (η , v) ≡ ⟦ σ ↑ˢ , ` 0 ⟧ˢ (η , v)
promote σ η v e =
  begin
    (η , v)
  ≡⟨ cong₂ _,_ e refl ⟩
    ⟦ σ ⟧ˢ η , v
  ≡⟨ cong₂ _,_ (sym (weakenˢ σ η v)) refl ⟩
    ⟦ σ ↑ˢ ⟧ˢ (η , v) , ⟦ ` 0 ⟧ (η , v)
  ≡⟨⟩
    ⟦ σ ↑ˢ , ` 0 ⟧ˢ (η , v)
  ∎

promote-M : ∀ (σ : Γ ⊒ Γ) (M : Γ ⊢ A) (η : ⟦ Γ ⟧ᵉ)
  → η ≡ ⟦ σ ⟧ˢ η
  → (η , ⟦ M ⟧ η) ≡ ⟦ σ ↑ˢ , M ↑ ⟧ˢ (η , ⟦ M ⟧ η)
promote-M σ M η e =
  begin
    η , ⟦ M ⟧ η
  ≡⟨ cong₂ _,_ e refl ⟩
    ⟦ σ ⟧ˢ η , ⟦ M ⟧ η
  ≡⟨ cong₂ _,_ (weakenˢ σ η (⟦ M ⟧ η)) (weaken M η (⟦ M ⟧ η)) ⟨
    ⟦ σ ↑ˢ ⟧ˢ (η , ⟦ M ⟧ η) , ⟦ M ↑ ⟧ (η , ⟦ M ⟧ η)
  ≡⟨⟩
    ⟦ σ ↑ˢ , M ↑ ⟧ˢ (η , ⟦ M ⟧ η)
  ∎

ƛ-lemma₁ : ∀ (z : Γ ⊢ B ↝ C) (σ : Γ ⊒ Γ) (N : Γ , A ⊢ B) (M : Γ ⊢ A) (η : ⟦ Γ ⟧ᵉ)
  → ⟦ z [ (ƛ N) · M ] ⟧ η ≡ ⟦ (z ↑ᶻ) [ N ] ⟧ (η , ⟦ M ⟧ η)
ƛ-lemma₁ z σ N M η = zip↑ z ((ƛ N) · M) N η (⟦ M ⟧ η) refl
```

# Soundness of Inline
```
inline : (σ : Γ ⊒ Γ)
         (z : Γ ⊢ A ↝ B) (z′ : Γ ⊢ A′ ↝ B) (zz : z ≽ z′)
         (M : Γ ⊢ A) (M′ : Γ ⊢ A′)
  → Inline σ zz M M′
  → (η : ⟦ Γ ⟧ᵉ)
  → η ≡ ⟦ σ ⟧ˢ η
  → ⟦ z ⟧ᶻ η (⟦ M ⟧ η) ≡ ⟦ z′ ⟧ᶻ η (⟦ M′ ⟧ η)
inline σ z .z .(idᶻᶻ z) .(` x) .(` x) (` x) η e = refl
inline σ z z′ zz (` x) N′ (`↓ r) η e =
  begin
    ⟦ z ⟧ᶻ η (⟦ ` x ⟧ η)
  ≡⟨ cong (⟦ z ⟧ᶻ η) (lookup-lemma x σ η e) ⟩
    ⟦ z ⟧ᶻ η (⟦ lookup σ x ⟧ η)
  ≡⟨ inline σ z z′ zz (lookup σ x) N′ r η e ⟩
    ⟦ z′ ⟧ᶻ η (⟦ N′ ⟧ η)
  ∎
inline σ □ □ □ (ƛ N) (ƛ N′) (ƛ□ t) η e =
  extensionality
    (λ v → inline (σ ↑ˢ , ` 0) □ □ □ N N′ t (η , v) (promote σ η v e))
inline σ (z · .M) (z′ · .M) (keep M zz) (ƛ N) (ƛ N′) (ƛ t) η e =
  begin
    ⟦ z · M ⟧ᶻ η (⟦ ƛ N ⟧ η)
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ ƛ N ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ N ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ cong₂ _$_ (sym (weakenᶻ z η (⟦ M ⟧ η))) refl ⟩
    ⟦ z ↑ᶻ ⟧ᶻ (η , ⟦ M ⟧ η) (⟦ N ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ inline (σ ↑ˢ , M ↑) (z ↑ᶻ) (z′ ↑ᶻ) (zz ↑ᶻᶻ) N N′ t (η , ⟦ M ⟧ η) (promote-M σ M η e) ⟩
    ⟦ z′ ↑ᶻ ⟧ᶻ (η , ⟦ M ⟧ η) (⟦ N′ ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ cong₂ _$_ (weakenᶻ z′ η (⟦ M ⟧ η)) refl ⟩
    ⟦ z′ ⟧ᶻ η (⟦ N′ ⟧ (η , ⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z′ ⟧ᶻ η (⟦ ƛ N′ ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z′ · M ⟧ᶻ η (⟦ ƛ N′ ⟧ η)
  ∎
inline σ (z · .M) z′ (drop M zz) (ƛ N) N′ (ƛ↓ t) η e =
  begin
    ⟦ z · M ⟧ᶻ η (⟦ ƛ N ⟧ η)
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ ƛ N ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ N ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ cong₂ _$_ (sym (weakenᶻ z η (⟦ M ⟧ η))) refl ⟩
    ⟦ z ↑ᶻ ⟧ᶻ (η , ⟦ M ⟧ η) (⟦ N ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ inline (σ ↑ˢ , M ↑) (z ↑ᶻ) (z′ ↑ᶻ) (zz ↑ᶻᶻ) N (N′ ↑) t (η , ⟦ M ⟧ η) (promote-M σ M η e) ⟩
    ⟦ z′ ↑ᶻ ⟧ᶻ (η , ⟦ M ⟧ η) (⟦ N′ ↑ ⟧ (η , ⟦ M ⟧ η))
  ≡⟨ cong₂ _$_ (weakenᶻ z′ η (⟦ M ⟧ η)) (weaken N′ η (⟦ M ⟧ η)) ⟩
    ⟦ z′ ⟧ᶻ η (⟦ N′ ⟧ η)
  ∎
inline σ z z′ zz (L · M) (L′ · M′) (r · s) η e =
  begin
    ⟦ z ⟧ᶻ η (⟦ L · M ⟧ η)
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ L ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z · M ⟧ᶻ η (⟦ L ⟧ η)
  ≡⟨ inline σ (z · M) (z′ · M) (keep M zz) L L′ r η e ⟩
    ⟦ z′ · M ⟧ᶻ η (⟦ L′ ⟧ η)
  ≡⟨⟩
    ⟦ z′ ⟧ᶻ η (⟦ L′ ⟧ η (⟦ M ⟧ η))
  ≡⟨ cong (λ ● → ⟦ z′ ⟧ᶻ η (⟦ L′ ⟧ η ●)) (inline σ □ □ □ M M′ s η e) ⟩
    ⟦ z′ ⟧ᶻ η (⟦ L′ ⟧ η (⟦ M′ ⟧ η))
  ≡⟨⟩
    ⟦ z′ ⟧ᶻ η (⟦ L′ · M′ ⟧ η)
  ∎
inline σ z z′ zz (L · M) N′ (r ·↓) η e =
  begin
    ⟦ z ⟧ᶻ η (⟦ L · M ⟧ η)
  ≡⟨⟩
    ⟦ z ⟧ᶻ η (⟦ L ⟧ η (⟦ M ⟧ η))
  ≡⟨⟩
    ⟦ z · M ⟧ᶻ η (⟦ L ⟧ η)
  ≡⟨ inline σ (z · M) z′ (drop M zz) L N′ r η e ⟩
    ⟦ z′ ⟧ᶻ η (⟦ N′ ⟧ η)
  ∎

inline⁺ : (M M′ : ∅ ⊢ A)
  → Inline⁺ M M′
  → ⟦ M ⟧ tt ≡ ⟦ M′ ⟧ tt
inline⁺ M M′ (r ↑ᵗ) = inline ∅ □ □ □ M M′ r tt refl
inline⁺ M M′ (_⨾_ {N = N} r s) = trans (inline⁺ M N r) (inline⁺ N M′ s)
```

# Annotation
```
data ann : Set where
  var : ann
  expand : ann → ann
  ƛ_ : ann → ann
  _·_ : ann → ann → ann
  _·↓ : ann → ann

data ann⁺ A : Set where
  _↑ᵗ : ann → ann⁺ A
  _⨾[_]_ : ann⁺ A → (∅ ⊢ A) → ann⁺ A → ann⁺ A
```

# Checking equality
```
_≟ᵗ_ : (A A′ : Type) → Maybe (A ≡ A′)
`ℕ ≟ᵗ `ℕ = just refl
(A ⇒ B) ≟ᵗ (A′ ⇒ B′) =
  do refl ← A ≟ᵗ A′
     refl ← B ≟ᵗ B′
     just refl
{-# CATCHALL #-}
C ≟ᵗ C′ = nothing

_≟ᵛ_ : (x x′ : Γ ∋ A) → Maybe (x ≡ x′)
Z ≟ᵛ Z = just refl
(S x) ≟ᵛ (S x′) =
  do refl ← x ≟ᵛ x′
     just refl
{-# CATCHALL #-}
x ≟ᵛ x′ = nothing

_≟_ : (M M′ : Γ ⊢ A) → Maybe (M ≡ M′)
(` x) ≟ (` x′) =
  do refl ← x ≟ᵛ x′
     just refl
(ƛ N) ≟ (ƛ N′) =
  do refl ← N ≟ N′
     just refl
(_·_ {A = A} L M) ≟ (_·_ {A = A′} L′ M′) =
  do refl ← A ≟ᵗ A′
     refl ← L ≟ L′
     refl ← M ≟ M′
     just refl
{-# CATCHALL #-}
M ≟ M′ = nothing

_≟ᶻ_ : (z z′ : Γ ⊢ A ↝ B) → Maybe (z ≡ z′)
□ ≟ᶻ □ = just refl
(z · M) ≟ᶻ (z′ · M′) =
  do refl ← z ≟ᶻ z′
     refl ← M ≟ M′
     just refl
{-# CATCHALL #-}
z ≟ᶻ z′ = nothing

_≟ᶻᶻ_ : (zz zz′ : z ≽ z′) → Maybe (zz ≡ zz′)
□ ≟ᶻᶻ □ = just refl
keep M zz ≟ᶻᶻ keep M′ zz′ =
  do refl ← M ≟ M′
     refl ← zz ≟ᶻᶻ zz′
     just refl
drop M zz ≟ᶻᶻ drop M′ zz′ =
  do refl ← M ≟ M′
     refl ← zz ≟ᶻᶻ zz′
     just refl
{-# CATCHALL #-}
zz ≟ᶻᶻ zz′ = nothing

```

Check aided by annotations
```
check : (a : ann)
        (σ : Γ ⊒ Γ)
        (zz : z ≽ z′)
        (M : Γ ⊢ A) (M′ : Γ ⊢ A′)
        → Maybe (Inline σ zz M M′)
check {A = A} {z = z} {A′ = A′} {z′ = z′} var σ zz  (` x) (` x′) =
  (do refl ← A ≟ᵗ A′
      refl ← x ≟ᵛ x′
      refl ← z ≟ᶻ z′
      refl ← zz ≟ᶻᶻ idᶻᶻ z
      just (` x))
check (expand a) σ zz (` x) M′ =
  (do r ← check a σ zz (lookup σ x) M′
      just (`↓ r))
check (ƛ a) σ □ (ƛ N) (ƛ N′) =
  (do t ← check a (σ ↑ˢ , ` Z) □ N N′
      just (ƛ□ t))
check (ƛ a) σ (keep M zz) (ƛ N) (ƛ N′)  =
  (do t ← check a (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N N′
      just (ƛ t))
check (ƛ a) σ (drop M zz) (ƛ N) N′  =
  (do t ← check a (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N (N′ ↑)
      just (ƛ↓ t))
check (a · b) σ zz (L ·[ A ] M) (L′ ·[ A′ ] M′) =
  (do refl ← A ≟ᵗ A′
      r ← check a σ (keep M zz) L L′
      s ← check b σ □ M M′
      just (r · s))
check (a ·↓) σ zz (L · M) N′ =
  (do r ← check a σ (drop M zz) L N′
      just (r ·↓))
{-# CATCHALL #-}
check a σ zz M M′ = nothing
```

# Top-level check
```
top-check : (a : ann) (M : ∅ ⊢ A) (M′ : ∅ ⊢ A)
            → Maybe (Inline ∅ □ M M′)
top-check a M M′  =  check a ∅ □ M M′

check⁺ : (a : ann⁺ A) (M M′ : ∅ ⊢ A) → Maybe (Inline⁺ M M′)
check⁺ (a ↑ᵗ) M M′ =
  do r ← check a ∅ □ M M′
     just (r ↑ᵗ)
check⁺ (a ⨾[ N ] b) M M′ =
  do r ← check⁺ a M N
     s ← check⁺ b N M′
     just (r ⨾ s)
```

# Lemmas
```
reflexiveᵗ : (A : Type) → A ≟ᵗ A ≡ just refl
reflexiveᵗ `ℕ = refl
reflexiveᵗ (A ⇒ B) rewrite reflexiveᵗ A | reflexiveᵗ B = refl

reflexiveᵛ : (x : Γ ∋ A) → x ≟ᵛ x ≡ just refl
reflexiveᵛ Z = refl
reflexiveᵛ (S x) rewrite reflexiveᵛ x = refl

reflexive : (M : Γ ⊢ A) → M ≟ M ≡ just refl
reflexive (` x) rewrite reflexiveᵛ x = refl
reflexive (ƛ N) rewrite reflexive N = refl
reflexive (_·_ {A = A} L M) rewrite reflexiveᵗ A | reflexive L | reflexive M = refl

reflexiveᶻ : (z : Γ ⊢ A ↝ B) → z ≟ᶻ z ≡ just refl
reflexiveᶻ □ = refl
reflexiveᶻ (z · M) rewrite reflexiveᶻ z | reflexive M = refl

reflexiveᶻᶻ : (zz : z ≽ z′) → zz ≟ᶻᶻ zz ≡ just refl
reflexiveᶻᶻ □ = refl
reflexiveᶻᶻ (keep M zz) rewrite reflexive M | reflexiveᶻᶻ zz = refl
reflexiveᶻᶻ (drop M zz) rewrite reflexive M | reflexiveᶻᶻ zz = refl
```

# Ziyang's Theorem
```
complete :
  (σ : Γ ⊒ Γ)
  (zz : z ≽ z′)
  (M : Γ ⊢ A)
  (M′ : Γ ⊢ A′)
  (s : Inline σ zz M M′)
  → ∃[ a ] (check a σ zz M M′ ≡ just s)
complete σ zz (L · M) N′ (r ·↓)
  with complete σ (drop M zz) L N′ r
... | (a , e)
  = (a ·↓ , hole)
  where
  hole : check (a ·↓) σ zz (L · M) N′ ≡ just (r ·↓)
  hole rewrite e = refl
complete {A = A} {z = z} σ .(idᶻᶻ z) .(` x) .(` x) (` x)
  = var , hole
  where
  hole : check var σ (idᶻᶻ z) (` x) (` x) ≡ just (` x)
  hole rewrite  reflexiveᵗ A | reflexiveᵛ x | reflexiveᶻ z | reflexiveᶻᶻ (idᶻᶻ z) = refl
complete σ zz (` x) M′ (`↓ s)
  with complete σ zz (lookup σ x) M′ s
... | (a , e)
  = (expand a , hole)
  where
  hole : check (expand a) σ zz (` x) M′ ≡ just (`↓ s)
  hole rewrite e = refl
complete σ □ (ƛ N) (ƛ N′) (ƛ□ t)
  with complete (σ ↑ˢ , ` Z) □ N N′ t
... | (a , e)
  = (ƛ a , hole)
  where
  hole : check (ƛ a) σ □ (ƛ N) (ƛ N′) ≡ just (ƛ□ t)
  hole rewrite e = refl
complete σ (drop M zz) (ƛ N) N′ (ƛ↓ t)
  with complete (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N (N′ ↑) t
... | (a , e)
  =  (ƛ a , hole)
  where
  hole : check (ƛ a) σ (drop M zz) (ƛ N) N′ ≡ just (ƛ↓ t)
  hole rewrite e = refl
complete σ (keep M zz) (ƛ N) (ƛ N′) (ƛ t)
  with complete (σ ↑ˢ , M ↑) (zz ↑ᶻᶻ) N N′ t
... | (a , e)
  = (ƛ a , hole)
  where
  hole : check (ƛ a) σ (keep M zz) (ƛ N) (ƛ N′) ≡ just (ƛ t)
  hole rewrite e = refl
complete σ zz (L ·[ A ] M) (L′ ·[ .A ] M′) (r · s)
  with complete σ (keep M zz) L L′ r | complete σ □ M M′ s
... | (a , e) | (b , f)
  = (a · b , hole)
  where
  hole : check (a · b) σ zz (L · M) (L′ · M′) ≡ just (r · s)
  hole rewrite reflexiveᵗ A | e | f = refl

complete⁺ :
  (M M′ : ∅ ⊢ A)
  (s : Inline⁺ M M′)
  → ∃[ a ] (check⁺ a M M′ ≡ just s)
complete⁺ M M′ (r ↑ᵗ)
  with complete ∅ □ M M′ r
... | (a , e)
  = (a ↑ᵗ) , hole
  where
  hole : check⁺ (a ↑ᵗ) M M′ ≡ just (r ↑ᵗ)
  hole rewrite e = refl
complete⁺ M M′ (_⨾_ {N = N} r s)
  with complete⁺ M N r | complete⁺ N M′ s
... | (a , e) | (b , f)
  = (a ⨾[ N ] b) , hole
  where
  hole : check⁺ (a ⨾[ N ] b) M M′ ≡ just (r ⨾ s)
  hole rewrite e | f = refl

-- E ::= □ | E₁[λx. E₂] t
data ECtx : Env → Env → Set where
  □ : ∀ {Γ} → ECtx Γ Γ

  -- E₁[λx. E₂] t
  bind : ∀ {Γ Δ Θ A}
       → ECtx Γ Δ → ECtx (Δ , A) Θ → Γ ⊢ A
       → ECtx Γ Θ

-- Fill the hole in ECtx with a term
plug : ∀ {Γ Δ A} → ECtx Γ Δ → Δ ⊢ A → Γ ⊢ A
plug □            N = N
plug (bind E F M) N = plug E (ƛ (plug F N)) · M

-- Weaken a term from the root's scope into the hole's scope.
into : ∀ {Γ Δ A} → ECtx Γ Δ → Γ ⊢ A → Δ ⊢ A
into □            N = N
into (bind E F M) N = into F ((into E N) ↑)

data Replace₁ : ∀ {Γ A B}
             → Γ ∋ A → Γ ⊢ A → Γ ⊢ B → Γ ⊢ B → Set where

  at : ∀ {Γ A} {x : Γ ∋ A} {V : Γ ⊢ A}
     → Replace₁ x V (` x) V

  under : ∀ {Γ A B C} {x : Γ ∋ A} {V : Γ ⊢ A}
            {N N′ : Γ , B ⊢ C}
        → Replace₁ (S x) (V ↑) N N′
        → Replace₁ x V (ƛ N) (ƛ N′)

  left : ∀ {Γ A B C} {x : Γ ∋ A} {V : Γ ⊢ A}
           {L L′ : Γ ⊢ B ⇒ C} {M : Γ ⊢ B}
       → Replace₁ x V L L′
       → Replace₁ x V (L · M) (L′ · M)

  right : ∀ {Γ A B C} {x : Γ ∋ A} {V : Γ ⊢ A}
            {L : Γ ⊢ B ⇒ C} {M M′ : Γ ⊢ B}
        → Replace₁ x V M M′
        → Replace₁ x V (L · M) (L · M′)

data Step : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where

  substitute : ∀ {Γ Δ A B}
                 (E : ECtx Γ Δ) (M : Γ ⊢ A)
                 {N N′ : Δ , A ⊢ B}
             → Replace₁ Z ((into E M) ↑) N N′
             → Step (plug E (ƛ N)  · M)
                    (plug E (ƛ N′) · M)

  drop : ∀ {Γ Δ A B}
           (E : ECtx Γ Δ) (M : Γ ⊢ A) (N : Δ ⊢ B)
       → Step (plug E (ƛ (N ↑)) · M)
              (plug E N)

  -- Allow either operation at any term position.

  under-ƛ : ∀ {Γ A B} {N N′ : Γ , A ⊢ B}
          → Step N N′
          → Step (ƛ N) (ƛ N′)

  under-·₁ : ∀ {Γ A B}
               {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
           → Step L L′
           → Step (L · M) (L′ · M)

  under-·₂ : ∀ {Γ A B}
               {L : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
           → Step M M′
           → Step (L · M) (L · M′)

data InlineSimple {Γ : Env} {A : Type} : Γ ⊢ A → Γ ⊢ A → Set where
  done : ∀ {M} → InlineSimple M M

  next : ∀ {L M N}
       → Step L M → InlineSimple M N → InlineSimple L N
```
