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
open import Function using (_∘_; case_of_; id)
open import Untyped.Equality using (DecEq; _≟_; decPointwise)
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation; convert; reflexive)
import Relation.Binary as Binary using (Decidable)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.String using (String; _++_)
open import Data.Fin using (Fin; suc; zero)
import Data.Fin as Fin using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.Product using (_×_; Σ; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to infixl 5 _,_)
open import Untyped.RenamingSubstitution using (_[_]; Sub; _↑ˢ; lifts; extend; weaken; sub)
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
open import Untyped.Purity
open import Untyped.Strictness
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

private variable
  L M N L′ M′ N′ : X ⊢

-- | Zipper
data _↝ (X : ℕ) : Set where
  □ : X ↝
  _·_ : X ↝ → (X ⊢) → X ↝

zip : X ↝ → X ⊢ → X ⊢
zip □ M = M
zip (z · N) M = zip z (M · N)

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
  drop : ∀ {z z′} (M : X ⊢) → z ≽ z′ → (z · M) ≽ z′

prez : {z z' : X ↝} →  z ≽ z' → X ↝
prez {z = z} _ = z

postz : {z z' : X ↝} →  z ≽ z' → X ↝
postz {z' = z'} _ = z'

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

```
private
  tail : {X Y : ℕ} → Sub (suc X) Y → Sub X Y
  tail σ x = σ (suc x)

subst : Fin X → X ⊢ → X ⊢ → X ⊢
subst* : Fin X → X ⊢ → List (X ⊢) → List (X ⊢)
subst x M (` y) with x ≟ y
... | yes _ = M
... | no _ = ` y
subst x M (ƛ t)         = ƛ (subst (suc x) (weaken M) t)
subst x M (t · u)       = subst x M t · subst x M u
subst x M (force t)     = force (subst x M t)
subst x M (delay t)     = delay (subst x M t)
subst x M (con tcn)     = con tcn
subst x M (builtin b)   = builtin b
subst x M error         = error
subst x M (constr i xs) = constr i (subst* x M xs)
subst x M (case N Ns)  = case (subst x M N) (subst* x M Ns)
subst* x M [] = []
subst* x M (N ∷ Ns) = subst x M N ∷ subst* x M Ns

subst-seq : {X Y : ℕ} → (Fin X → Fin Y) → Sub X Y → Y ⊢ → Y ⊢
subst-seq* : {X Y : ℕ} → (Fin X → Fin Y) → Sub X Y → List (Y ⊢) → List (Y ⊢)
subst-seq {zero} X<Y σ M = M
subst-seq {suc n} X<Y σ M = subst-seq (X<Y ∘ suc) (tail σ) (subst (X<Y zero) (σ zero) M)
subst-seq* X<Y σ [] = []
subst-seq* X<Y σ (M ∷ Ms) = subst-seq X<Y σ M ∷ subst-seq* X<Y σ Ms
```

# Effect-safe

Suppose we have a multi-let with `n` bindings:

   (ƛ₁ ƛ₂ ... ƛₙ N) · error · M₂ · ... · Mₙ

And suppose we are inlining the first binding, that binds `error`. We have to
check that `N` is strict in the bound variable. While `x ∈↓ M` approximates if
an expression M is strict in x,  it does not look under lambdas, so it will not
accept (multi-)lets.

`StrictLetₙ x z M` expects a term that starts with a multi-let, where the
arguments are in zipper `z` and the corresponding lambdas in `M`. It will fall
back to `∈↓` once it reaches the body of the let.

```
data StrictLetₙ {Y : ℕ} (n : Fin X) : Y ↝ → X ⊢ → Set where
  body :
    n ∈↓ M
    -----------------------
    → StrictLetₙ n z M

  binder :
    StrictLetₙ (suc n) z M
    ----------------------------
    → StrictLetₙ n (z · N) (ƛ M)
```

Corresponding decision procedure:

```
check-StrictLetₙ :
  {Y : ℕ} (n : Fin X) (z : Y ↝) (M : X ⊢) → Dec (StrictLetₙ n z M)
check-StrictLetₙ n z M
  with n ∈↓? M
... | yes eval = yes (body eval)
... | no ¬eval
  with z | (ƛ? ⋯) M
... | □ | _ = no (λ { (body eval) → ¬eval eval})
... | z · N | no ¬ƛ = no λ { (body eval) → ¬eval eval; (binder _) → ¬ƛ inhabitant}
... | z · N | yes (ƛ! (match! M))
  with check-StrictLetₙ (suc n) z M
... | no ¬eib = no λ {(body eval) → ¬eval eval; (binder eib) → ¬eib eib }
... | yes eib = yes (binder eib)
```

Given a binding in a multi-let `(ƛ ... ƛ N) · M₁ · ... · Mₙ`, this speifies the
compiler's check for when it is safe to remove the argument (in terms of effects
like error or non-termination).

```
data EffectSafe (M : X ⊢) (z : X ↝) (N : suc X ⊢) : Set where
  no-effects :
    Pure M
    ----------------
    → EffectSafe M z N

  var-evaluated :
    StrictLetₙ zero z N
    ----------------
    → EffectSafe M z N
```

If `M` is pure, it has no effects so it is always safe to inline it
(`no-effects`). Alternatively, if variable `x` is guaranteed to be evaluated in
`N`, any effects of `M` will be retained (`var-evaluated`).

```
check-EffectSafe
  : (σ : Sub X X)
  → (z : X ↝)
  → (M : X ⊢)
  → (N : suc X ⊢)
  → Proof? (EffectSafe (subst-seq id σ M) z N)
check-EffectSafe σ z M N =
  case isPure? (subst-seq id σ M) of λ where
    (yes pure) → proof (no-effects pure)
    (no _) → case check-StrictLetₙ zero z N of λ where
      (yes eval) → proof (var-evaluated eval)
      (no _) → abort InlineT (subst-seq id σ M) (zip z ((ƛ N) · M))
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
      EffectSafe (subst-seq id σ M) (prez zz) N
    → Inline (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N (weaken N′)
    ---------------------------------------
    → Inline σ (drop M zz) (ƛ N) N′

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
   do safe ← check-EffectSafe σ (prez zz) M N
      t ← check (extend (σ ↑ˢ) (weaken M)) N (zz ↑ᶻᶻ) h (weaken N′)
      proof (ƛ↓ safe t)

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

-- postulate debug : ∀ {i} {X : ℕ} {A : Set i} → X ⊢ → A → A

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

`check-EffectSafe` will find a `EffectSafe` proof if there is one:

```
check-EffectSafe-complete :
    ∀ {σ : Sub X X} {z : X ↝} {M : X ⊢} {N : suc X ⊢}
    → (p : EffectSafe (subst-seq id σ M) z N)
    → ∃ λ p' → check-EffectSafe σ z M N ≡ proof p'
check-EffectSafe-complete {σ = σ} {z = z} {M = M} {N = N} p with isPure? (subst-seq id σ M)
... | yes pure' = no-effects pure' , refl
... | no ¬pure
  with p
... | no-effects pure = ⊥-elim (¬pure pure)
... | var-evaluated eval with check-StrictLetₙ zero z N
... | yes eval' = var-evaluated eval' , refl
... | no ¬eval = ⊥-elim (¬eval eval)
```

If there is a `Inline` proof, thereexist hints such that `check` will find a
proof of `Inline`.

```
-- completePointwise :
--   (σ : Sub X X)
--   (zz : z ≽ z′)
--   (Ms M′s : List (X ⊢))
--   (rs : Pointwise (Inline σ zz) Ms M′s)
--   → ∃[ hs ] (∃[ rs' ] (checkPointwise hs σ zz Ms M′s ≡ proof rs'))
-- 
-- complete :
--   (σ : Sub X X)
--   (zz : z ≽ z′)
--   (M M′ : X ⊢)
--   (s : Inline σ zz M M′)
--   → ∃[ h ] (∃[ s' ] (check σ M zz h M′ ≡ proof s'))
-- complete {z = z} σ .(idᶻᶻ z) .(` x) .(` x) (` x) = (var , (_ , e′))
--   where
--   e′ : check σ (` x) (idᶻᶻ z) var (` x) ≡ proof (` x)
--   e′ rewrite reflexiveᴬ Fin._≟_ x | reflexiveᴬ _≟ᶻ_ z | reflexiveᶻᶻ (idᶻᶻ z) = refl
-- complete σ zz (` x) M′ (`↓ s)
--   with complete σ zz (σ x) M′ s
-- ... | (h , (s' , e)) = (expand h , (_ , e′))
--   where
--   e′ : check σ (` x) zz (expand h) M′ ≡ proof (`↓ s')
--   e′ rewrite e = refl
-- complete σ □ (ƛ N) (ƛ N′) (ƛ□ t)
--   with complete (lifts σ) □ N N′ t
-- ... | (h , (s' , e)) = (ƛ h , (_ , e′))
--   where
--   e′ : check σ (ƛ N) □ (ƛ h) (ƛ N′) ≡ proof (ƛ□ s')
--   e′ rewrite e = refl
-- complete σ (keep M zz) (ƛ N) (ƛ N′) (ƛ t)
--   with complete (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N N′ t
-- ... | (h , (s' , e)) = (ƛ h , (_ , e′))
--   where
--   e′ : check σ (ƛ N) (keep M zz) (ƛ h) (ƛ N′) ≡ proof (ƛ s')
--   e′ rewrite e = refl
-- complete σ (drop M zz) (ƛ N) N′ (ƛ↓ safe t)
--   with
--     check-EffectSafe-complete safe
--   | complete (extend (σ ↑ˢ) (weaken M)) (zz ↑ᶻᶻ) N (weaken N′) t
-- ... | safe' , eq | (h , (s' , e)) = (h , (_ , e′))
--   where
--   e′ : check σ (ƛ N) (drop M zz) h N′ ≡ proof (ƛ↓ safe' s')
--   e′ rewrite e = ?
-- complete σ zz (L · M) (L′ · M′) (r · s)
--   with complete σ (keep M zz) L L′ r | complete σ □ M M′ s
-- ... | (h , (r' , e)) | (h′ , (s' , e′)) = (h · h′ , (_ , e″))
--   where
--   e″ : check σ (L · M) zz (h · h′) (L′ · M′) ≡ proof (r' · s')
--   e″ rewrite e | e′ = refl
-- complete σ zz (L · M) N′ (r ·↓)
--   with complete σ (drop M zz) L N′ r
-- ... | (h , (s' , e)) = (h ·↓ , (_ , e′))
--   where
--   e′ : check σ (L · M) zz (h ·↓) N′ ≡ proof (s' ·↓)
--   e′ rewrite e = refl
-- complete σ zz (force M) (force M′) (force r)
--   with complete σ □ M M′ r
-- ... | (h , (s' , e)) = (force h , (_ , e′))
--   where
--   e′ : check σ (force M) zz (force h) (force M′) ≡ proof (force s')
--   e′ rewrite e = refl
-- complete σ zz (delay M) (delay M′) (delay r)
--   with complete σ □ M M′ r
-- ... | (h , (s' , e)) = (delay h , (_ , e′))
--   where
--   e′ : check σ (delay M) zz (delay h) (delay M′) ≡ proof (delay s')
--   e′ rewrite e = refl
-- complete σ zz (con c) .(con c) con = (con , (_ , e))
--   where
--   e : check σ (con c) zz con (con c) ≡ proof con
--   e rewrite reflexiveᴬ _≟_ c = refl
-- complete σ zz (builtin b) .(builtin b) builtin = (builtin , (_ , e))
--   where
--   e : check σ (builtin b) zz builtin (builtin b) ≡ proof builtin
--   e rewrite reflexiveᴬ _≟_ b = refl
-- complete σ zz (constr i Ms) (constr .i M′s) (constr rs)
--   with completePointwise σ □ Ms M′s rs
-- ... | (hs , (rs' , e)) = (constr hs , (_ , e′))
--   where
--   e′ : check σ (constr i Ms) zz (constr hs) (constr i M′s) ≡ proof (constr rs')
--   e′ rewrite reflexiveᴬ _≟_ i | e = refl
-- complete σ zz (case M Ms) (case M′ M′s) (case r rs)
--   with complete σ □ M M′ r | completePointwise σ □ Ms M′s rs
-- ... | (h , (r' , e)) | (hs , (rs' , e′)) = (case h hs , (_ , e″))
--   where
--   e″ : check σ (case M Ms) zz (case h hs) (case M′ M′s) ≡ proof (case r' rs')
--   e″ rewrite e | e′ = refl
-- complete σ zz error error error = (error , (_ , refl))
-- 
-- completePointwise σ zz [] [] Pointwise.[] = ([] , (_ , refl))
-- completePointwise σ zz (M ∷ Ms) (M′ ∷ M′s) (p Pointwise.∷ ps)
--   with complete σ zz M M′ p | completePointwise σ zz Ms M′s ps
-- ... | (h , (p' , e)) | (hs , (ps' , e′)) = ((h ∷ hs) , (_ , e″))
--   where
--   e″ : checkPointwise (h ∷ hs) σ zz (M ∷ Ms) (M′ ∷ M′s) ≡ proof (p' Pointwise.∷ ps')
--   e″ rewrite e | e′ = refl
```

Replaying the inliner using the pre-term and hints to obtain the post-term:

```
open import Data.Maybe using (map; ap)

-- TODO use zipper
replay : ∀{X} → Sub X X → InlineHints → X ⊢ → Maybe (X ⊢)
replay* : ∀{X} → Sub X X → List InlineHints → List (X ⊢) → Maybe (List (X ⊢))
replay σ var (` x) = just (` x)
replay _ var _ = nothing
replay σ (expand h) (` x) = replay σ h (σ x)
replay _ (expand _) _ = nothing
replay σ (ƛ h) (ƛ M) = map ƛ (replay (lifts σ) h M)
replay σ (ƛ _) _ = nothing
replay σ (h · l) (M · N) = ap (ap (just _·_) (replay σ h M)) (replay σ l N)
replay σ (_ · _) _ = nothing
replay σ (h ·↓) (M · N) = replay σ h M
replay σ (h ·↓) _ = nothing
replay σ (force h) (force M) = map force (replay σ h M)
replay σ (force h) _ = nothing
replay σ (delay h) (delay M) = map delay (replay σ h M)
replay σ (delay h) _ = nothing
replay σ con (con x) = just (con x)
replay σ con _ = nothing
replay σ builtin (builtin b) = just (builtin b)
replay σ builtin _ = nothing
replay σ error error = just error
replay σ error _ = nothing
replay σ (constr hs) (constr i Ms) = map (constr i) (replay* σ hs Ms)
replay σ (constr hs) _ = nothing
replay σ (case h hs) (case M Ms) = ap (ap (just case) (replay σ h M)) (replay* σ hs Ms)
replay σ (case h hs) _ = nothing
replay* σ [] [] = just []
replay* σ [] (_ ∷ _) = nothing
replay* {X} σ (h ∷ hs) (M ∷ Ms) = ap (ap (just (_∷_)) (replay σ h M)) (replay* σ hs Ms)
replay* σ (_ ∷ _) [] = nothing
```

## Examples

Convenenience patterns and constructors:

```
open import Relation.Nullary using (True; toWitness)
import Data.Nat.Properties as ℕ
open import Data.Fin using (#_; fromℕ<)

pattern let₁ M₁ N                      = ƛ N · M₁
pattern let₂ M₁ M₂ N                   = (ƛ (ƛ N)) · M₁ · M₂
pattern let₃ M₁ M₂ M₃ N                = (ƛ (ƛ (ƛ N))) · M₁ · M₂ · M₃
pattern let₄ M₁ M₂ M₃ M₄ N             = (ƛ (ƛ (ƛ (ƛ N)))) · M₁ · M₂ · M₃ · M₄

v : ∀ m {n} {m<n : True (m ℕ.<? n)} → n ⊢
v _ {m<n = m<n} = ` (fromℕ< (toWitness m<n))
```


Multi-lets

```
module ExMulti where
  pre : 0 ⊢
  pre =
    let₂
      error
      error
      (v 1 · v 0)

  post : 0 ⊢
  post = error · error

  pre-post : Proof? (Inline (λ()) □ pre post)
  pre-post = top-check hints pre post
    where
      hints : InlineHints
      hints = (expand error · expand error) ·↓ ·↓
```

```
module ExNested where
  pre : 0 ⊢
  pre = let₁
         error
         (let₁
           (v 0)
           (v 1 · v 0))
  post : 0 ⊢
  post = error · error

  -- h01 : InlineHints
  -- h01 = (expand error · expand error) ·↓ ·↓
  open import Untyped.Strictness

  pre-post : Inline (λ()) □ pre post
  pre-post = ƛ↓ (var-evaluated (body (·ᵣ var)))
            (ƛ↓ (var-evaluated (body (·ᵣ var))) (`↓ error · `↓ (`↓ error)) ·↓) ·↓


  pre-post' : Proof? (Inline (λ()) □ pre post)
  pre-post' = top-check hints pre post
    where
      hints : InlineHints
      hints = (expand error · (expand (expand error))) ·↓ ·↓
```



