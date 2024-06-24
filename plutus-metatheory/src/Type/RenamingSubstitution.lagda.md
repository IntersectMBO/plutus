---
title: Type Renaming and Substitution
layout: page
---

```
module Type.RenamingSubstitution where
```

## Imports

```
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using (Vec;[];_∷_;lookup) 
open import Data.List using (List;[];_∷_)
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
  renaming (subst to substEq) 

open import Utils using (*;J;K)
open import Type using (Ctx⋆;_,⋆_;∅;Φ;Ψ;_⊢⋆_;_∋⋆_;S;Z)
open _⊢⋆_
```

## Type renaming

Types can contain functions and as such are subject to a nontrivial equality relation. To
explain the computation equation (the β-rule) we need to define substitution for a single
type variable in a type. A type renaming is a function from type variables in one context to
type variables in another. We only need the ability to
introduce new variable on the right hand side of the context. The simplicity of the
definition makes it easy to work with and we get some properties for free that we would
have to pay for with a first order representation, such as not needing to define a lookup
function, and we inherit the properties of functions provided by η-equality, such as
associativity of composition, for free. Note that even though
renamings are functions we do not require our metatheory (Agda’s type system) to support
functional extensionality. We only ever need to make use of an equation
between renamings on a point (a variable) and therefore need only a pointwise version
of equality on functions to work with equality of renamings and substitutions.

```
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J
```

Let `ρ` range over renamings.
```
variable
  ρ ρ' : Ren Φ Ψ
```

As we are going to push renamings through types we need to be able to push them
under a binder. To do this safely the newly bound variable should remain untouched and
other renamings should be shifted by one to accommodate this. (Note: this is
called `lift⋆` in the [paper](https://intersectmbo.github.io/plutus/resources/plutus-core-spec.pdf#page=8) ).

```
ext : Ren Φ Ψ
      -----------------------------
    → ∀ {K} → Ren (Φ ,⋆ K) (Ψ ,⋆ K)
ext ρ Z      =  Z
ext ρ (S α)  =  S (ρ α)
```

# Apply a type renaming to a type.

This is defined by recursion on the type. Observe that we lift the renaming when
we go under a binder and actually apply the renaming when we hit a variable. 

```
ren : Ren Φ Ψ
      -----------------------
    → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
ren-List : Ren Φ Ψ
      -----------------------
    → ∀ {J} → List (Φ ⊢⋆ J) → List (Ψ ⊢⋆ J)
ren-VecList : Ren Φ Ψ
      -----------------------
    → ∀ {n J} → Vec (List (Φ ⊢⋆ J)) n → Vec (List (Ψ ⊢⋆ J)) n

ren ρ (` α)       = ` (ρ α)
ren ρ (Π B)       = Π (ren (ext ρ) B)
ren ρ (A ⇒ B)     = ren ρ A ⇒ ren ρ B
ren ρ (ƛ B)       = ƛ (ren (ext ρ) B)
ren ρ (μ A B)     = μ (ren ρ A) (ren ρ B)
ren ρ (^ x)       = ^ x
ren ρ (con c)     = con (ren ρ c) 
ren ρ (A · B)     = ren ρ A · ren ρ B
ren ρ (SOP xss)   = SOP (ren-VecList ρ xss)

ren-List ρ [] = []
ren-List ρ (x ∷ xs) = ren ρ x ∷ ren-List ρ xs
ren-VecList ρ [] = []
ren-VecList ρ (xs ∷ xss) = ren-List ρ xs ∷ ren-VecList ρ xss
```

Weakening is a special case of renaming. We apply the renaming S which does double
duty as the variable constructor, if we check the type of S we see that it is a renaming.
Weakening shifts all the existing variables one place to the left in the context.

```
weaken : Φ ⊢⋆ J
         -----------
       → Φ ,⋆ K ⊢⋆ J
weaken = ren S
```

## Renaming proofs

First functor law for `ext`

```
ext-id : (α : Φ ,⋆ K ∋⋆ J)
         -----------------
       → ext id α ≡ α
ext-id Z     = refl
ext-id (S α) = refl
```

This congruence lemma and analogous ones for `exts`, `ren`, and
`sub` avoids the use of extensionality when reasoning about equal
renamings/substitutions as we only need a pointwise version of
equality. If we used the standard library's `cong` we would need to
postulate extensionality and our equality proofs wouldn't compute. I
learnt this from Conor McBride.

```
ext-cong : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{J K}(α : Φ ,⋆ J ∋⋆ K)
           --------------------------------
         → ext ρ α ≡ ext ρ' α
ext-cong p Z     = refl
ext-cong p (S α) = cong S (p α)
```

Congruence lemma for `ren`

```
ren-cong : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{K}(A : Φ ⊢⋆ K)
           --------------------------------
         → ren ρ A ≡ ren ρ' A
ren-cong-List : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{K}(As : List (Φ ⊢⋆ K))
           --------------------------------
         → ren-List ρ As ≡ ren-List ρ' As
ren-cong-VecList : (∀ {J}(α : Φ ∋⋆ J) → ρ α ≡ ρ' α)
         → ∀{n K}(Tss : Vec (List (Φ ⊢⋆ K)) n)
           --------------------------------
         → ren-VecList ρ Tss ≡ ren-VecList ρ' Tss

ren-cong p (` α)   = cong ` (p α)
ren-cong p (Π A)   = cong Π (ren-cong (ext-cong p) A)
ren-cong p (A ⇒ B) = cong₂ _⇒_ (ren-cong p A) (ren-cong p B)
ren-cong p (ƛ A)   = cong ƛ (ren-cong (ext-cong p) A)
ren-cong p (A · B) = cong₂ _·_ (ren-cong p A) (ren-cong p B)
ren-cong p (μ A B) = cong₂ μ (ren-cong p A) (ren-cong p B)
ren-cong p (^ x)   = refl
ren-cong p (con c) = cong con (ren-cong p c)
ren-cong p (SOP xss) = cong SOP (ren-cong-VecList p xss)

ren-cong-List p [] = refl
ren-cong-List p (x ∷ xs) = cong₂ _∷_ (ren-cong p x) (ren-cong-List p xs)
ren-cong-VecList p [] = refl
ren-cong-VecList p (xs ∷ xss) = cong₂ _∷_ (ren-cong-List p xs) (ren-cong-VecList p xss)
```

First functor law for `ren`

```
ren-id : (A : Φ ⊢⋆ J)
         ------------
       → ren id A ≡ A
ren-id-List : 
         (As : List (Φ ⊢⋆ J))
         --------------------
       → ren-List id As ≡ As       
ren-id-VecList : ∀{n}
         (Tss : Vec (List (Φ ⊢⋆ J)) n)
         --------------------
       → ren-VecList id Tss ≡ Tss  

ren-id (` α)     = refl
ren-id (Π A)     = cong Π (trans (ren-cong ext-id A) (ren-id A))
ren-id (A ⇒ B)   = cong₂ _⇒_(ren-id A) (ren-id B)
ren-id (ƛ A)     = cong ƛ (trans (ren-cong ext-id A) (ren-id A))
ren-id (A · B)   = cong₂ _·_ (ren-id A) (ren-id B)
ren-id (μ A B)   = cong₂ μ (ren-id A) (ren-id B)
ren-id (^ x)     = refl
ren-id (con c)   = cong con (ren-id c)
ren-id (SOP xss) = cong SOP (ren-id-VecList xss) 

ren-id-List [] = refl
ren-id-List (x ∷ xs) = cong₂ _∷_ (ren-id x) (ren-id-List xs)
ren-id-VecList [] = refl
ren-id-VecList (xs ∷ xss) = cong₂ _∷_ (ren-id-List xs) (ren-id-VecList xss)
```

Second functor law for `ext`

```
ext-comp : ∀{J K}(x : Φ ,⋆ K ∋⋆ J)
           ---------------------------------
         → ext (ρ ∘ ρ') x ≡ ext ρ (ext ρ' x)
ext-comp Z     = refl
ext-comp (S x) = refl
```

Second functor law for `ren`

```
ren-comp : ∀{J}(A : Φ ⊢⋆ J)
           ---------------------------------
         → ren (ρ ∘ ρ') A ≡ ren ρ (ren ρ' A)
ren-comp-List : ∀{J}(As : List (Φ ⊢⋆ J))
           ---------------------------------
         → ren-List (ρ ∘ ρ') As ≡ ren-List ρ (ren-List ρ' As)
ren-comp-VecList : ∀{n J}(Tss : Vec (List (Φ ⊢⋆ J)) n)
           -------------------------------------------
         → ren-VecList (ρ ∘ ρ') Tss ≡ ren-VecList ρ (ren-VecList ρ' Tss)
ren-comp (` x)   = refl
ren-comp (Π A)   = cong Π (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A ⇒ B) = cong₂ _⇒_ (ren-comp A) (ren-comp B)
ren-comp (ƛ A)   = cong ƛ (trans (ren-cong ext-comp A) (ren-comp A))
ren-comp (A · B) = cong₂ _·_ (ren-comp A) (ren-comp B)
ren-comp (μ A B) = cong₂ μ (ren-comp A) (ren-comp B)
ren-comp (^ x)   = refl
ren-comp (con c) = cong con (ren-comp c)
ren-comp (SOP xss) = cong SOP (ren-comp-VecList xss)

ren-comp-List [] = refl
ren-comp-List (x ∷ xs) = cong₂ _∷_ (ren-comp x) (ren-comp-List xs)
ren-comp-VecList [] = refl
ren-comp-VecList (xs ∷ xss) = cong₂ _∷_ (ren-comp-List xs) (ren-comp-VecList xss)
```

## Type substitution

A type substitution is a mapping of type variables to types. Much of this section
mirrors functions in the Type section above, so the explainations and design intent
are the same. There are [Fusion Proofs](#fusion-proofs) below.

```
Sub : Ctx⋆ → Ctx⋆ → Set
Sub Φ Ψ = ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J
```

Let `σ` range over substitutions:
```
variable
  σ σ' : Sub Φ Ψ
```

Extending a type substitution — used when going under a binder. (This is called `lifts` in the [paper](https://intersectmbo.github.io/plutus/resources/plutus-core-spec.pdf#page=8) ).

```
exts : Sub Φ Ψ
       -----------------------------
     → ∀ {K} → Sub (Φ ,⋆ K) (Ψ ,⋆ K)
exts σ Z      = ` Z
exts σ (S α)  = weaken (σ α)
```

Apply a type substitution to a type.

```
sub : Sub Φ Ψ
      -----------------------
    → ∀ {J} → Φ ⊢⋆ J → Ψ ⊢⋆ J
sub-List : Sub Φ Ψ
      -----------------------
    → ∀ {J} → List (Φ ⊢⋆ J) → List (Ψ ⊢⋆ J)
sub-VecList : Sub Φ Ψ
      -----------------------
    → ∀ {n J} → Vec (List (Φ ⊢⋆ J)) n → Vec (List (Ψ ⊢⋆ J)) n


sub σ (` α)   = σ α
sub σ (Π B)   = Π (sub (exts σ) B)
sub σ (A ⇒ B) = sub σ A ⇒ sub σ B
sub σ (ƛ B)   = ƛ (sub (exts σ) B)
sub σ (A · B) = sub σ A · sub σ B
sub σ (μ A B) = μ (sub σ A) (sub σ B)
sub σ (^ x)   = ^ x
sub σ (con c) = con (sub σ c)
sub σ (SOP xss) = SOP (sub-VecList σ xss) 

sub-List σ [] = []
sub-List σ (x ∷ xs) = sub σ x ∷ sub-List σ xs
sub-VecList σ [] = []
sub-VecList σ (xs ∷ xss) = sub-List σ xs ∷ sub-VecList σ xss
```

Extend a substitution with an additional type (analogous to `cons` for
backward lists)

```
sub-cons : Sub Φ Ψ
         → ∀{J}(A : Ψ ⊢⋆ J)
           ----------------
         → Sub (Φ ,⋆ J) Ψ
sub-cons f A Z = A
sub-cons f A (S x) = f x
```

A special case is substitution a type for the outermost free variable:
```
_[_] : Φ ,⋆ K ⊢⋆ J
     → Φ ⊢⋆ K 
       -----------
     → Φ ⊢⋆ J
B [ A ] =  sub (sub-cons ` A) B
```

## Type Substitution Proofs

Extending the identity substitution yields the identity substitution

```
exts-id : (α : Φ ,⋆ K ∋⋆ J)
          -----------------
        → exts ` α ≡ ` α 
exts-id Z     = refl
exts-id (S α) = refl
```

Congruence lemma for `exts`

```
exts-cong : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
          → ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
            --------------------------------
          → exts σ α ≡ exts σ' α
exts-cong p Z     = refl
exts-cong p (S α) = cong (ren S) (p α)
```

Congruence lemma for `sub`

```
sub-cong : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
         → ∀{K}(A : Φ ⊢⋆ K)
           --------------------------------
         → sub σ A ≡ sub σ' A
sub-cong-List : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
         → ∀{K}(As : List (Φ ⊢⋆ K))
           --------------------------------
         → sub-List σ As ≡ sub-List σ' As
sub-cong-VecList : (∀ {J}(α : Φ ∋⋆ J) → σ α ≡ σ' α)
         → ∀{n K}(Tss : Vec (List (Φ ⊢⋆ K)) n)
           --------------------------------
         → sub-VecList σ Tss ≡ sub-VecList σ' Tss

sub-cong p (` α)   = p α
sub-cong p (Π A)   = cong Π (sub-cong (exts-cong p) A)
sub-cong p (A ⇒ B) = cong₂ _⇒_ (sub-cong p A) (sub-cong p B)
sub-cong p (ƛ A)   = cong ƛ (sub-cong (exts-cong p) A)
sub-cong p (A · B) = cong₂ _·_ (sub-cong p A) (sub-cong p B)
sub-cong p (μ A B) = cong₂ μ (sub-cong p A) (sub-cong p B)
sub-cong p (^ x)   = refl
sub-cong p (con c) = cong con (sub-cong p c) 
sub-cong p (SOP xss) = cong SOP (sub-cong-VecList p xss)

sub-cong-List p [] = refl
sub-cong-List p (x ∷ xs) = cong₂ _∷_ (sub-cong p x) (sub-cong-List p xs)
sub-cong-VecList p [] = refl
sub-cong-VecList p (xs ∷ xss) = cong₂ _∷_ (sub-cong-List p xs) (sub-cong-VecList p xss)
```

First relative monad `law` for `sub`

```
sub-id : (A : Φ ⊢⋆ J)
         ------------
       → sub ` A ≡ A
sub-id-List : 
         (As : List (Φ ⊢⋆ J))
         --------------------
       → sub-List ` As ≡ As
sub-id-VecList : ∀{n} 
         (Tss : Vec (List (Φ ⊢⋆ J)) n)
         --------------------
       → sub-VecList ` Tss ≡ Tss

sub-id (` α)      = refl
sub-id (Π A)      = cong Π (trans (sub-cong exts-id A) (sub-id A))
sub-id (A ⇒ B)    = cong₂ _⇒_ (sub-id A) (sub-id B)
sub-id (ƛ A)      = cong ƛ (trans (sub-cong exts-id A) (sub-id A))
sub-id (A · B)    = cong₂ _·_ (sub-id A) (sub-id B)
sub-id (μ A B)    = cong₂ μ (sub-id A) (sub-id B)
sub-id (^ x)      = refl
sub-id (con c)    = cong con (sub-id c) 
sub-id (SOP xss)  = cong SOP (sub-id-VecList xss)

sub-id-List [] = refl
sub-id-List (x ∷ xs) = cong₂ _∷_ (sub-id x) (sub-id-List xs)
sub-id-VecList [] = refl
sub-id-VecList (xs ∷ xss) = cong₂ _∷_ (sub-id-List xs) (sub-id-VecList xss)
```
## Fusion proofs

Fusion of `exts` and `ext`

```
exts-ext : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
           ---------------------------------
         → exts (σ ∘ ρ) α ≡ exts σ (ext ρ α)
exts-ext Z     = refl
exts-ext (S α) = refl
```

Fusion for `sub` and `ren`

```
sub-ren : ∀{J}(A : Φ ⊢⋆ J)
          -------------------------------
        → sub (σ ∘ ρ) A ≡ sub σ (ren ρ A)
sub-ren-List :  ∀{J}
          (As : List (Φ ⊢⋆ J))
          -------------------------------
        → sub-List (σ ∘ ρ) As ≡ sub-List σ (ren-List ρ As)

sub-ren-VecList :  ∀{n J} →
          (Tss : Vec (List (Φ ⊢⋆ J)) n)
          -------------------------------
        → sub-VecList (σ ∘ ρ) Tss ≡ sub-VecList σ (ren-VecList ρ Tss)

sub-ren (` α)     = refl
sub-ren (Π A)     = cong Π (trans (sub-cong exts-ext A) (sub-ren A))
sub-ren (A ⇒ B)   = cong₂ _⇒_ (sub-ren A) (sub-ren B)
sub-ren (ƛ A)     = cong ƛ (trans (sub-cong exts-ext A) (sub-ren A))
sub-ren (A · B)   = cong₂ _·_ (sub-ren A) (sub-ren B)
sub-ren (μ A B)   = cong₂ μ (sub-ren A) (sub-ren B)
sub-ren (^ x)     = refl
sub-ren (con c)   = cong con (sub-ren c)
sub-ren (SOP xss) = cong SOP (sub-ren-VecList xss) 

sub-ren-List [] = refl
sub-ren-List (x ∷ xs) = cong₂ _∷_ (sub-ren x) (sub-ren-List xs)
sub-ren-VecList [] = refl
sub-ren-VecList (xs ∷ xss) = cong₂ _∷_ (sub-ren-List xs) (sub-ren-VecList xss)
```

Fusion for `exts` and `ext`

```
ren-ext-exts : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
               -------------------------------------------
             → exts (ren ρ ∘ σ) α ≡ ren (ext ρ) (exts σ α)
ren-ext-exts Z     = refl
ren-ext-exts (S α) = trans (sym (ren-comp _)) (ren-comp _)
```

Fusion for `ren` and `sub`

```
ren-sub : ∀{J}(A : Φ ⊢⋆ J)
          -----------------------------------
        → sub (ren ρ ∘ σ) A ≡ ren ρ (sub σ A)
ren-sub-List : ∀ {J}
          (As : List (Φ ⊢⋆ J))
          ---------------------------------------------------------------
        → sub-List (ren ρ ∘ σ) As ≡ ren-List ρ (sub-List σ As)

ren-sub-VecList : ∀ {n J}
          (Tss : Vec (List (Φ ⊢⋆ J)) n)
          ---------------------------------------------------------------
        → sub-VecList (ren ρ ∘ σ) Tss ≡ ren-VecList ρ (sub-VecList σ Tss)


ren-sub (` α)     = refl
ren-sub (Π A)     = cong Π (trans (sub-cong ren-ext-exts  A) (ren-sub A))
ren-sub (A ⇒ B)   = cong₂ _⇒_ (ren-sub A) (ren-sub B)
ren-sub (ƛ A)     = cong ƛ (trans (sub-cong ren-ext-exts A) (ren-sub A))
ren-sub (A · B)   = cong₂ _·_ (ren-sub A) (ren-sub B)
ren-sub (μ A B)   = cong₂ μ (ren-sub A) (ren-sub B)
ren-sub (^ x)     = refl
ren-sub (con c)   = cong con (ren-sub c)
ren-sub (SOP xss) = cong SOP (ren-sub-VecList xss) 

ren-sub-List [] = refl
ren-sub-List (x ∷ xs) = cong₂ _∷_ (ren-sub x) (ren-sub-List xs)

ren-sub-VecList [] = refl
ren-sub-VecList (xs ∷ xss) = cong₂ _∷_ (ren-sub-List xs) (ren-sub-VecList xss)
```

Fusion of two `exts`

```
extscomp : ∀{J K}(α : Φ ,⋆ K ∋⋆ J)
           ----------------------------------------------
         → exts (sub σ ∘ σ') α ≡ sub (exts σ) (exts σ' α)
extscomp         Z     = refl
extscomp {σ' = σ'} (S α) = trans (sym (ren-sub (σ' α))) (sub-ren (σ' α))
```

Fusion of substitutions/third relative monad law for `sub`

```
sub-comp : ∀{J}(A : Φ ⊢⋆ J)
           -------------------------------------
         → sub (sub σ ∘ σ') A ≡ sub σ (sub σ' A)
sub-com-List : ∀ {J} 
                (As : List (Φ ⊢⋆ J))
                ------------------------------------------------------------------     
              → sub-List (sub σ ∘ σ') As ≡ sub-List σ (sub-List σ' As)

sub-com-VecList : ∀ {n J} 
                (Tss : Vec (List (Φ ⊢⋆ J)) n) 
                ------------------------------------------------------------------     
              → sub-VecList (sub σ ∘ σ') Tss ≡ sub-VecList σ (sub-VecList σ' Tss)


sub-comp (` x)      = refl
sub-comp (Π A)      = cong Π (trans (sub-cong extscomp A) (sub-comp A))
sub-comp (A ⇒ B)    = cong₂ _⇒_ (sub-comp A) (sub-comp B)
sub-comp (ƛ A)      = cong ƛ (trans (sub-cong extscomp A) (sub-comp A))
sub-comp (A · B)    = cong₂ _·_ (sub-comp A) (sub-comp B)
sub-comp (μ A B)    = cong₂ μ (sub-comp A) (sub-comp B)
sub-comp (^ x)      = refl
sub-comp (con c)    = cong con (sub-comp c)
sub-comp (SOP xss)  = cong SOP (sub-com-VecList xss) 

sub-com-List [] = refl
sub-com-List (x ∷ xs) = cong₂ _∷_ (sub-comp x) (sub-com-List xs)
sub-com-VecList [] = refl
sub-com-VecList (xs ∷ xss) = cong₂ _∷_ (sub-com-List xs) (sub-com-VecList xss)
```

Commuting `sub-cons` and `ren`

```
ren-sub-cons : (ρ : Ren Φ Ψ)
             → (A : Φ ⊢⋆ K)
             → (α : Φ ,⋆ K ∋⋆ J)
               -------------------------------------------------------
             → sub-cons ` (ren ρ A) (ext ρ α) ≡ ren ρ (sub-cons ` A α)
ren-sub-cons ρ A Z     = refl
ren-sub-cons ρ A (S α) = refl
```

Commuting `sub-cons` and `sub`

```
sub-sub-cons : (σ : Sub Φ Ψ)
             → (M : Φ ⊢⋆ K)
             → (α : Φ ,⋆ K ∋⋆ J)
               --------------------------------------------------------------
             → sub (sub-cons ` (sub σ M)) (exts σ α) ≡ sub σ (sub-cons ` M α)
sub-sub-cons σ M Z     = refl
sub-sub-cons σ M (S α) = trans (sym (sub-ren (σ α))) (sub-id (σ α))
```
## Additional lemmas

A useful lemma for fixing up the types when renaming a `wrap` or `unwrap`

```
ren-μ : (ρ⋆ : Ren Φ Ψ)
      → (A : Φ ⊢⋆ _)
      → (B : Φ ⊢⋆ K)
      → -----------------------------------------------------
        ren ρ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
        ≡
        ren ρ⋆ A · ƛ (μ (weaken (ren ρ⋆ A)) (` Z)) · ren ρ⋆ B
ren-μ ρ⋆ A B = cong
  (λ X → ren ρ⋆ A · ƛ (μ X (` Z)) · ren ρ⋆ B)
  (trans (sym (ren-comp A)) (ren-comp A))
```

A useful lemma for fixing up the types when renaming a type application


```
ren-Π : ∀(A : Φ ⊢⋆ K)(B : Φ ,⋆ K ⊢⋆ J)(ρ : Ren Φ Ψ)
      → ren (ext ρ) B [ ren ρ A ] ≡ ren ρ (B [ A ])
ren-Π A B ρ =
  trans (sym (sub-ren B)) (trans (sub-cong (ren-sub-cons ρ A) B) (ren-sub B))

```

A useful lemma for fixing up the types when substituting into a `wrap`
or `unwrap`

```
sub-μ : (σ⋆ : Sub Φ Ψ)
      → (A : Φ ⊢⋆ _)
      → (B : Φ ⊢⋆ K)
        -----------------------------------------------------
      → sub σ⋆ (A · ƛ (μ (weaken A) (` Z)) · B)
        ≡
        sub σ⋆ A · ƛ (μ (weaken (sub σ⋆ A)) (` Z)) · sub σ⋆ B
sub-μ σ⋆ A B = cong
  (λ X → sub σ⋆ A · ƛ (μ X (` Z)) · sub σ⋆ B)
  (trans (sym (sub-ren A)) (ren-sub A))
```

A useful lemma when substituting into a type application

```
sub-Π : ∀(A : Φ ⊢⋆ K)(B : Φ ,⋆ K ⊢⋆ J)(σ : Sub Φ Ψ)
      → sub (exts σ) B [ sub σ A ] ≡ sub σ (B [ A ])
sub-Π A B σ =
  trans (sym (sub-comp B)) (trans (sub-cong (sub-sub-cons σ A) B) (sub-comp B))
```

Substituting in the empty type context is the same as doing nothing.
```
sub-∅ : (A : ∅ ⊢⋆ J)  → (x : Sub ∅ ∅) → sub x A ≡ A
sub-∅ A x = trans (sub-cong (λ ()) A) (sub-id A)
```

If we start from a type in an empty context, we may weaken it to any context,
and then we have two lemmas.
```
sub∅ : ∀{Φ K} → ∅ ⊢⋆ K → Φ ⊢⋆ K
sub∅ t = sub (λ()) t 

sub∅-ren : ∀{K} (t : ∅ ⊢⋆ K) (ρ : Ren Φ Ψ) → sub∅ t ≡ ren ρ (sub∅ t)
sub∅-ren t ρ = trans (sub-cong (λ ()) t) (ren-sub t)

sub∅-sub : ∀{K} (t : ∅ ⊢⋆ K) (ρ : Sub Φ Ψ) → sub∅ t ≡ sub ρ (sub∅ t)
sub∅-sub t ρ = trans (sub-cong (λ ()) t) (sub-comp t)
```

Some properties relating uses of lookup on VecList-functions with List-functions

```
lookup-ren-VecList : ∀ {n}
              → (ρ : Ren Φ Ψ)
              → (e : Fin n)
              → (Tss : Vec (List (Φ ⊢⋆ *)) n)
                --------------------------------------------
              → lookup (ren-VecList ρ Tss) e ≡ ren-List ρ (lookup Tss e)
lookup-ren-VecList ρ zero (_ ∷ _) = refl
lookup-ren-VecList ρ (suc e) (_ ∷ Tss) = lookup-ren-VecList ρ e Tss

lookup-sub-VecList : ∀ {n}
              → (σ : Sub Φ Ψ)
              → (e : Fin n)
              → (Tss : Vec (List (Φ ⊢⋆ *)) n)
                --------------------------------------------
              → lookup (sub-VecList σ Tss) e ≡ sub-List σ (lookup Tss e)
lookup-sub-VecList σ zero (_ ∷ _) = refl
lookup-sub-VecList σ (suc e) (_ ∷ Tss) = lookup-sub-VecList σ e Tss
```
