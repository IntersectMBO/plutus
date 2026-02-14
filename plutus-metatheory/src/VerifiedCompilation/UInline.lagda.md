---
title: VerifiedCompilation.UForceDelay
layout: page
---

# Force-Delay Translation Phase
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
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; _++_)
open import Data.Fin using (Fin; suc; zero)
import Data.Fin as Fin using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
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
open import VerifiedCompilation.Certificate using (Proof?; _>>=_; InlineHints; var; expand; ƛ; _·_; _·↓; force; delay; con; builtin; error; constr; case; abort; proof; inlineT)
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
      (r : Inline σ zz M M′)
    → -------------------------------
      Inline σ zz (force M) (force M′)

  delay :
      (r : Inline σ zz M M′)
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
      (rs : Pointwise (Inline σ zz) Ms M′s)
    → -------------------------------
      Inline σ zz (constr i Ms) (constr i M′s)

  case :
      ∀ {Ms M′s}
      (r  : Inline σ zz M M′)
      (rs : Pointwise (Inline σ zz) Ms M′s)
    → -------------------------------
      Inline σ zz (case M Ms) (case M′ M′s)

  error : Inline σ zz error error
```

# Check aided by hints

```
ppr : ∀{X} → X ⊢ → String
ppr x = prettyPrintUTm (extricateU x)

pprList : ∀{X} → List (X ⊢) → String
pprList' : ∀{X} → List (X ⊢) → String
pprList' [] = ""
pprList' (x ∷ xs) = ppr x ++ " , " ++ pprList' xs

pprList xs = "[" ++ pprList' xs ++ "]"

checkPointwise :
        (as : List InlineHints)
        (σ : Sub X X)
        (zz : z ≽ z′)
        (Ms M′s : List (X ⊢))
        → Proof? (Pointwise (Inline σ zz) Ms M′s)

check : (a : InlineHints)
        (σ : Sub X X)
        (zz : z ≽ z′)
        (M M′ : X ⊢)
        → Proof? (Inline σ zz M M′)
check {z = z} {z′ = z′} var σ zz M@(` x) M′@(` x′)
  with x Fin.≟ x′ | z ≟ᶻ z′
... | yes refl | yes refl
    with zz ≟ᶻᶻ idᶻᶻ z
...   | just refl = proof (` x)
...   | nothing = abort inlineT (ppr M) (ppr M′)
check var σ zz M@(` x) M′@(` x′)
    | _ | _ = abort inlineT (ppr M) (ppr M′)

check (expand a) σ zz (` x) M′ =
   do r ← check a σ zz (σ x) M′
      proof (`↓ r)

check (ƛ a) σ □ (ƛ N) (ƛ N′) =
   do t ← check a (lifts σ) □ N N′
      proof (ƛ□ t)

check (ƛ a) σ (keep M zz) (ƛ N) (ƛ N′)  =
   do t ← check a (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N N′
      proof (ƛ t)

check a σ (drop M zz) (ƛ N) N′  =
   do t ← check a (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N (weaken N′)
      proof (ƛ↓ t)

check (a · b) σ zz (L · M) (L′ · M′) =
   do r ← check a σ (keep M zz) L L′
      s ← check b σ □ M M′
      proof (r · s)

check (a ·↓) σ zz (L · M) N′ =
   do r ← check a σ (drop M zz) L N′
      proof (r ·↓)

check (force a) σ zz (force M) (force M′) =
   do r ← check a σ zz M M′
      proof (force r)

check (delay a) σ zz (delay M) (delay M′) =
   do r ← check a σ zz M M′
      proof (delay r)

check con σ zz M@(con c) M′@(con c′)
  with c ≟ c′
... | yes refl = proof con
... | no  _ = abort inlineT (ppr M) (ppr M′)

check builtin σ zz M@(builtin b) M′@(builtin b′)
  with b ≟ b′
... | yes refl = proof builtin
... | no  _ = abort inlineT (ppr M) (ppr M′)

check (constr as) σ zz M@(constr i Ms) M′@(constr i′ M′s) with i ≟ i′
... | yes refl =
   do rs ← checkPointwise as σ zz Ms M′s
      proof (constr rs)
... | no _ = abort inlineT (ppr M) (ppr M′)

check (case a as) σ zz (case M Ms) (case M′ M′s) =
  do r ← check a σ zz M M′
     rs ← checkPointwise as σ zz Ms M′s
     proof (case r rs)

check error σ zz error error = proof error

check a σ zz M M′ = abort inlineT (ppr M) (ppr M′)

checkPointwise [] σ zz [] [] = proof Pointwise.[]
checkPointwise (a ∷ as) σ zz (M ∷ Ms) (M′ ∷ M′s) =
   do p ← check a σ zz M M′
      ps ← checkPointwise as σ zz Ms M′s
      proof (p Pointwise.∷ ps)
checkPointwise _ _ _ Ms M′s = abort inlineT (pprList Ms) (pprList M′s)
```

# Top-level check
```
top-check : (a : InlineHints) (M M′ : 0 ⊢)
            → Proof? (Inline (λ()) □ M M′)
top-check a M M′ = check a (λ()) □ M M′
```
