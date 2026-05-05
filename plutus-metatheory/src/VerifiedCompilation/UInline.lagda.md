---
title: VerifiedCompilation.UInline
layout: page
---

# Inline Phase
```
module VerifiedCompilation.UInline where

```
## Imports

```
open import Function using (_∘_)
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews using (Pred; isCase?; isApp?; isLambda?; isForce?; isBuiltin?; isConstr?; isDelay?; isTerm?; allTerms?; iscase; isapp; islambda; isforce; isbuiltin; isconstr; isterm; allterms; isdelay)
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _++_)
open import Data.Fin using (Fin; suc; zero)
import Data.Fin as Fin using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to infixl 5 _,_)
open import Untyped.RenamingSubstitution using (_[_]; Sub; _↑ˢ; lifts; extend; weaken)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; extricateU; extricateUList)
open import RawU using (Untyped)
open import Evaluator.Base using (prettyPrintUTm)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped.RenamingSubstitution using (weaken)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import VerifiedCompilation.Certificate using (Proof?; _>>=_; InlineHints; var; expand; ƛ; _·_; _·↓; force; delay; con; builtin; error; constr; case; abort; proof; InlineT)
```

# Zippers, and relating two zippers

```
infix 4 _≽_
infix 8 _↝

variable
  X Y : ℕ

variable
  x y : Fin X

variable
  σ : Sub X Y

variable
  L M N L′ M′ N′ : X ⊢

-- | Zipper
data _↝ (X : ℕ) : Set where
  □ : X ↝
  _·_ : X ↝ → (X ⊢) → X ↝

variable
  z z′ : X ↝

_↑ᶻ : X ↝ → (suc X) ↝
□ ↑ᶻ = □
(z · M) ↑ᶻ = (z ↑ᶻ) · weaken M

injᶻˡ : (z · M ≡ z′ · M′) → z ≡ z′
injᶻˡ refl = refl

injᶻʳ : (z · M ≡ z′ · M′) → M ≡ M′
injᶻʳ refl = refl

_≟ᶻ_ : DecidableEquality (X ↝)
□ ≟ᶻ □ = yes refl
(z · M) ≟ᶻ (z′ · M′) with z ≟ᶻ z′ | M ≟ M′
... | yes refl | yes refl = yes refl
... | no z≠z′ | _ = no (z≠z′ ∘ injᶻˡ)
... | yes refl | no M≠M′ = no (M≠M′ ∘ injᶻʳ)
(z · M) ≟ᶻ □ = no λ()
□ ≟ᶻ (z′ · M′) = no λ()

-- | Relating two zippers
data _≽_ {X : ℕ} : X ↝ → X ↝ → Set where
  □ : □ ≽ □
  keep : ∀ {z z′} (M : X ⊢) → z ≽ z′ → (z · M) ≽ (z′ · M)
  drop : ∀ {z z′} (M : X ⊢) → z ≽ z′ → (z · M) ≽ (z′ · M)

variable
  zz : z ≽ z′

_↑ᶻᶻ : z ≽ z′ → (z ↑ᶻ) ≽ (z′ ↑ᶻ)
□ ↑ᶻᶻ = □
(keep M zᵃ) ↑ᶻᶻ = keep (weaken M) (zᵃ ↑ᶻᶻ)
(drop M zᵃ) ↑ᶻᶻ = drop (weaken M) (zᵃ ↑ᶻᶻ)

idᶻᶻ : (z : X ↝) → z ≽ z
idᶻᶻ □ = □
idᶻᶻ (z · M) = keep M (idᶻᶻ z)

-- We could define `_≟ᶻᶻ_ : DecidableEquality (z ≽ z′)` instead, but it's much longer.
_≟ᶻᶻ_ : (zz zz′ : z ≽ z′) → Maybe (zz ≡ zz′)
□ ≟ᶻᶻ □ = just refl
keep M zz ≟ᶻᶻ keep M′ zz′ with M ≟ M′ | zz ≟ᶻᶻ zz′
... | yes refl | just refl = just refl
... | _ | _ = nothing
drop M zz ≟ᶻᶻ drop M′ zz′ with M ≟ M′ | zz ≟ᶻᶻ zz′
... | yes refl | just refl = just refl
... | _ | _ = nothing
{-# CATCHALL #-}
zz ≟ᶻᶻ zz′ = nothing
```

# Inline relation

```
data Inline {X : ℕ} :
  (σ : Sub X X)
  {z z′ : X ↝}
  (zz : z ≽ z′)
  (M M′ : X ⊢)
  → Set where

  ` :
      (x : Fin X)
    → -----------------------------
      Inline σ (idᶻᶻ z) (` x) (` x)

  `↓ :
      (r : Inline σ zz (σ x) M′)
    → -----------------------------
      Inline σ zz (` x) M′

  ƛ□ :
      Inline (lifts σ) □ N N′
    → -----------------------------
      Inline σ □ (ƛ N) (ƛ N′)

  ƛ :
      (t : Inline (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N N′)
    → ---------------------------------------
      Inline σ (keep M zz) (ƛ N) (ƛ N′)

  ƛ↓ :
      (t : Inline (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N (weaken N′))
    → ---------------------------------------
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

  -- The following constructors are for compatible closure

  force :
      (r : Inline σ □ M M′)
    → -------------------------------
      Inline σ zz (force M) (force M′)

  delay :
      (r : Inline σ □ M M′)
    → -------------------------------
      Inline σ zz (delay M) (delay M′)

  con :
      ∀ {c}
    → -------------------------------
      Inline σ zz (con c) (con c)

  builtin :
      ∀ {b}
    → -------------------------------
      Inline σ zz (builtin b) (builtin b)

  constr :
      ∀ {i Ms M′s}
      (rs : Pointwise (Inline σ □) Ms M′s)
    → -------------------------------
      Inline σ zz (constr i Ms) (constr i M′s)

  case :
      ∀ {Ms M′s}
      (r  : Inline σ □ M M′)
      (rs : Pointwise (Inline σ □) Ms M′s)
    → -------------------------------
      Inline σ zz (case M Ms) (case M′ M′s)

  error : Inline σ zz error error
```

# Check aided by hints

The order of `check`'s arguments is important to ensure the completeness proof works.
In particular:

- `M` must be before `h` for `check σ (ƛ N) (drop M zz) h N′` to be reducible.
  Splitting on `h` before `M` would cause reduction of this term to be stuck, since
  it doesn't match on `h`.
- `M` must be before `zz` for `check σ (L · M) zz (h ·↓) N′` to be reducible.
  Splitting on `zz` before `M` would cause reduction of this term to be stuck, since
  it doesn't match on `zz`.

The position of `σ` doesn't matter since no clause matches on it.


```
checkPointwise :
        (hs : List InlineHints)
        (σ : Sub X X)
        (zz : z ≽ z′)
        (Ms M′s : List (X ⊢))
        → Proof? (Pointwise (Inline σ zz) Ms M′s)

check : (σ : Sub X X)
        (M : X ⊢)
        (zz : z ≽ z′)
        (h : InlineHints)
        (M′ : X ⊢)
        → Proof? (Inline σ zz M M′)
check {z = z} {z′ = z′} σ M@(` x) zz var M′@(` x′)
  with x Fin.≟ x′ | z ≟ᶻ z′
... | yes refl | yes refl
    with zz ≟ᶻᶻ idᶻᶻ z
...   | just refl = proof (` x)
...   | nothing = abort InlineT M M′
check σ M@(` x) zz var M′@(` x′)
    | _ | _ = abort InlineT M M′

check σ (` x) zz (expand h) M′ =
   do r ← check σ (σ x) zz h M′
      proof (`↓ r)

check σ (ƛ N) □ (ƛ h) (ƛ N′) =
   do t ← check (lifts σ) N □ h N′
      proof (ƛ□ t)

check σ (ƛ N) (keep M zz) (ƛ h) (ƛ N′)  =
   do t ← check (extend (σ ↑ˢ) (weaken M)) N (zz ↑ᶻᶻ) h N′
      proof (ƛ t)

check σ (ƛ N) (drop M zz) h N′ =
   do t ← check (extend (σ ↑ˢ) (weaken M)) N (zz ↑ᶻᶻ) h (weaken N′)
      proof (ƛ↓ t)

check σ (L · M) zz (h · h′) (L′ · M′) =
   do r ← check σ L (keep M zz) h L′
      s ← check σ M □ h′ M′
      proof (r · s)

check σ (L · M) zz (h ·↓) N′ =
   do r ← check σ L (drop M zz) h N′
      proof (r ·↓)

check σ (force M) zz (force h) (force M′) =
   do r ← check σ M □ h M′
      proof (force r)

check σ (delay M) zz (delay h) (delay M′) =
   do r ← check σ M □ h M′
      proof (delay r)

check σ M@(con c) zz con M′@(con c′)
  with c ≟ c′
... | yes refl = proof con
... | no  _ = abort InlineT M M′

check σ M@(builtin b) zz builtin M′@(builtin b′)
  with b ≟ b′
... | yes refl = proof builtin
... | no  _ = abort InlineT M M′

check σ M@(constr i Ms) zz (constr hs) M′@(constr i′ M′s) with i ≟ i′
... | yes refl =
   do rs ← checkPointwise hs σ □ Ms M′s
      proof (constr rs)
... | no _ = abort InlineT M M′

check σ (case M Ms) zz (case h hs) (case M′ M′s) =
  do r ← check σ M □ h M′
     rs ← checkPointwise hs σ □ Ms M′s
     proof (case r rs)

check σ error zz error error = proof error

check σ M zz h M′ = abort InlineT M M′

checkPointwise [] σ zz [] [] = proof Pointwise.[]
checkPointwise (h ∷ hs) σ zz (M ∷ Ms) (M′ ∷ M′s) =
   do p ← check σ M zz h M′
      ps ← checkPointwise hs σ zz Ms M′s
      proof (p Pointwise.∷ ps)
checkPointwise _ _ _ Ms M′s = abort InlineT Ms M′s
```

# Top-level check
```
top-check : (h : InlineHints) (M M′ : 0 ⊢)
            → Proof? (Inline (λ()) □ M M′)
top-check h M M′ = check (λ()) M □ h M′
```

# Lemmas
```
reflexiveᴬ : {A : Set} → (_≟_ : DecidableEquality A) → (a : A) → (a ≟ a) ≡ yes refl
reflexiveᴬ _≟_ a with a ≟ a
... | yes refl = refl
... | no ¬p = ⊥-elim (¬p refl)

reflexiveᶻᶻ : (zz : z ≽ z′) → zz ≟ᶻᶻ zz ≡ just refl
reflexiveᶻᶻ □ = refl
reflexiveᶻᶻ (keep M zz) rewrite reflexiveᴬ _≟_ M | reflexiveᶻᶻ zz = refl
reflexiveᶻᶻ (drop M zz) rewrite reflexiveᴬ _≟_ M | reflexiveᶻᶻ zz = refl
```

# Completeness

```
completePointwise :
  (σ : Sub X X)
  (zz : z ≽ z′)
  (Ms M′s : List (X ⊢))
  (rs : Pointwise (Inline σ zz) Ms M′s)
  → ∃[ hs ] (checkPointwise hs σ zz Ms M′s ≡ proof rs)

complete :
  (σ : Sub X X)
  (zz : z ≽ z′)
  (M M′ : X ⊢)
  (s : Inline σ zz M M′)
  → ∃[ h ] (check σ M zz h M′ ≡ proof s)
complete {z = z} σ .(idᶻᶻ z) .(` x) .(` x) (` x) = (var , e′)
  where
  e′ : check σ (` x) (idᶻᶻ z) var (` x) ≡ proof (` x)
  e′ rewrite reflexiveᴬ Fin._≟_ x | reflexiveᴬ _≟ᶻ_ z | reflexiveᶻᶻ (idᶻᶻ z) = refl
complete σ zz (` x) M′ (`↓ s)
  with complete σ zz (σ x) M′ s
... | (h , e) = (expand h , e′)
  where
  e′ : check σ (` x) zz (expand h) M′ ≡ proof (`↓ s)
  e′ rewrite e = refl
complete σ □ (ƛ N) (ƛ N′) (ƛ□ t)
  with complete (lifts σ) □ N N′ t
... | (h , e) = (ƛ h , e′)
  where
  e′ : check σ (ƛ N) □ (ƛ h) (ƛ N′) ≡ proof (ƛ□ t)
  e′ rewrite e = refl
complete σ (keep M zz) (ƛ N) (ƛ N′) (ƛ t)
  with complete (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N N′ t
... | (h , e) = (ƛ h , e′)
  where
  e′ : check σ (ƛ N) (keep M zz) (ƛ h) (ƛ N′) ≡ proof (ƛ t)
  e′ rewrite e = refl
complete σ (drop M zz) (ƛ N) N′ (ƛ↓ t)
  with complete (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N (weaken N′) t
... | (h , e) = (h , e′)
  where
  e′ : check σ (ƛ N) (drop M zz) h N′ ≡ proof (ƛ↓ t)
  e′ rewrite e = refl
complete σ zz (L · M) (L′ · M′) (r · s)
  with complete σ (keep M zz) L L′ r | complete σ □ M M′ s
... | (h , e) | (h′ , e′) = (h · h′ , e″)
  where
  e″ : check σ (L · M) zz (h · h′) (L′ · M′) ≡ proof (r · s)
  e″ rewrite e | e′ = refl
complete σ zz (L · M) N′ (r ·↓)
  with complete σ (drop M zz) L N′ r
... | (h , e) = (h ·↓ , e′)
  where
  e′ : check σ (L · M) zz (h ·↓) N′ ≡ proof (r ·↓)
  e′ rewrite e = refl
complete σ zz (force M) (force M′) (force r)
  with complete σ □ M M′ r
... | (h , e) = (force h , e′)
  where
  e′ : check σ (force M) zz (force h) (force M′) ≡ proof (force r)
  e′ rewrite e = refl
complete σ zz (delay M) (delay M′) (delay r)
  with complete σ □ M M′ r
... | (h , e) = (delay h , e′)
  where
  e′ : check σ (delay M) zz (delay h) (delay M′) ≡ proof (delay r)
  e′ rewrite e = refl
complete σ zz (con c) .(con c) con = (con , e)
  where
  e : check σ (con c) zz con (con c) ≡ proof con
  e rewrite reflexiveᴬ _≟_ c = refl
complete σ zz (builtin b) .(builtin b) builtin = (builtin , e)
  where
  e : check σ (builtin b) zz builtin (builtin b) ≡ proof builtin
  e rewrite reflexiveᴬ _≟_ b = refl
complete σ zz (constr i Ms) (constr .i M′s) (constr rs)
  with completePointwise σ □ Ms M′s rs
... | (hs , e) = (constr hs , e′)
  where
  e′ : check σ (constr i Ms) zz (constr hs) (constr i M′s) ≡ proof (constr rs)
  e′ rewrite reflexiveᴬ _≟_ i | e = refl
complete σ zz (case M Ms) (case M′ M′s) (case r rs)
  with complete σ □ M M′ r | completePointwise σ □ Ms M′s rs
... | (h , e) | (hs , e′) = (case h hs , e″)
  where
  e″ : check σ (case M Ms) zz (case h hs) (case M′ M′s) ≡ proof (case r rs)
  e″ rewrite e | e′ = refl
complete σ zz error error error = (error , refl)

completePointwise σ zz [] [] Pointwise.[] = ([] , refl)
completePointwise σ zz (M ∷ Ms) (M′ ∷ M′s) (p Pointwise.∷ ps)
  with complete σ zz M M′ p | completePointwise σ zz Ms M′s ps
... | (h , e) | (hs , e′) = ((h ∷ hs) , e″)
  where
  e″ : checkPointwise (h ∷ hs) σ zz (M ∷ Ms) (M′ ∷ M′s) ≡ proof (p Pointwise.∷ ps)
  e″ rewrite e | e′ = refl
```
