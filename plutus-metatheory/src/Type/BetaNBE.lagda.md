---
title: Type.BetaNBE
layout: page
---
```
module Type.BetaNBE where
```

## Imports

```

open import Function using (_∘_;id)
open import Data.Vec using (Vec;[];_∷_) renaming (map to vmap)
open import Data.List using (List;[];_∷_;map)
open import Data.Sum using (_⊎_;inj₁;inj₂)

open import Utils using (Kind;*;_⇒_;♯)
open import Type using (Ctx⋆;_,⋆_;_⊢⋆_;_∋⋆_;Z;S)
open _⊢⋆_
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;renNe)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.RenamingSubstitution using (Ren)
import Builtin.Constant.Type as Syn
import Builtin.Constant.Type as Nf
```

Values are defined by induction on kind. At kind # and * they are
inert and defined to be just normal forms. At function kind they are
either neutral or Kripke functions

```
Val : Ctx⋆ → Kind → Set
Val Φ *       = Φ ⊢Nf⋆ *
Val Φ ♯       = Φ ⊢Nf⋆ ♯
Val Φ (σ ⇒ τ) = Φ ⊢Ne⋆ (σ ⇒ τ) ⊎ ∀ {Ψ} → Ren Φ Ψ → Val Ψ σ → Val Ψ τ
```

We can embed neutral terms into values at any kind using reflect.
reflect is quite simple in this version of NBE and not mutually
defined with reify.

```
reflect : ∀{Φ σ} → Φ ⊢Ne⋆ σ → Val Φ σ
reflect {σ = ♯}     n = ne n
reflect {σ = *}     n = ne n
reflect {σ = σ ⇒ τ} n = inj₁ n
```

A shorthand for creating a new fresh variable as a value which we need
in reify

```
fresh : ∀ {Φ σ} → Val (Φ ,⋆ σ) σ
fresh = reflect (` Z)
```

Renaming for values

```
renVal : ∀ {σ Φ Ψ} → Ren Φ Ψ → Val Φ σ → Val Ψ σ
renVal {*}     ψ n        = renNf ψ n
renVal {♯}     ψ n        = renNf ψ n
renVal {σ ⇒ τ} ψ (inj₁ n) = inj₁ (renNe ψ n)
renVal {σ ⇒ τ} ψ (inj₂ f) = inj₂ λ ρ' →  f (ρ' ∘ ψ)
```

Weakening for values

```
weakenVal : ∀ {σ Φ K} → Val Φ σ → Val (Φ ,⋆ K) σ
weakenVal = renVal S
```

Reify takes a value and yields a normal form.

```
reify : ∀ {σ Φ} → Val Φ σ → Φ ⊢Nf⋆ σ
reify {*}     n         = n
reify {♯}     n         = n
reify {σ ⇒ τ} (inj₁ n)  = ne n
reify {σ ⇒ τ} (inj₂ f)  = ƛ (reify (f S fresh)) -- has a name been lost here?
```

An environment is a mapping from variables to values

```
Env : Ctx⋆ → Ctx⋆ → Set
Env Ψ Φ = ∀{J} → Ψ ∋⋆ J → Val Φ J
```

'cons' for environments

```
_,,⋆_ : ∀{Ψ Φ} → (σ : Env Φ Ψ) → ∀{K}(A : Val Ψ K) → Env (Φ ,⋆ K) Ψ
(σ ,,⋆ A) Z     = A
(σ ,,⋆ A) (S α) = σ α
```

```
exte : ∀ {Φ Ψ} → Env Φ Ψ → (∀ {K} → Env (Φ ,⋆ K) (Ψ ,⋆ K))
exte η = (weakenVal ∘ η) ,,⋆ fresh
{-
-- this version would be more analogous to ext and exts but would
-- require changing some proofs for terms
exte η Z      = fresh
exte η (S α)  = weakenVal (η α)
-}
```


Application for values. As values at function type can be semantic
functions or neutral terms we need this function to unpack them. If
the function is neutral we create a neutral application by reifying
the value and applying the neutral application constructor, then we
refect the neutral application into a value. If the function is a
semantic function we apply it to the identity renaming and then to
the argument. In this case, the function and argument are in the same
context so we do not need the Kripke extension, hence the identity
renaming.

```
_·V_ : ∀{Φ K J} → Val Φ (K ⇒ J) → Val Φ K → Val Φ J
inj₁ n ·V v = reflect (n · reify v)
inj₂ f ·V v = f id v
```

Evaluation a term in an environment yields a value. The most
interesting cases are ƛ where we introduce a new Kripke function that
will evaluate when it receives an argument and Π/μ where we need to go
under the binder and extend the environment before evaluating and
reifying.

```
eval : ∀{Φ Ψ K} → Ψ ⊢⋆ K → Env Ψ Φ → Val Φ K

eval-List : ∀{Φ Ψ K} → List (Ψ ⊢⋆ K) → Env Ψ Φ → List (Val Φ K)
eval-VecList : ∀{Φ Ψ K n} → Vec (List (Ψ ⊢⋆ K)) n → Env Ψ Φ → Vec (List (Val Φ K)) n

eval (` α)     η = η α
eval (Π B)     η = Π (reify (eval B (exte η)))
eval (A ⇒ B)   η = reify (eval A η) ⇒ reify (eval B η)
eval (ƛ B)     η = inj₂ λ ρ v → eval B ((renVal ρ ∘ η) ,,⋆ v)
eval (A · B)   η = eval A η ·V eval B η
eval (μ A B)   η = μ (reify (eval A η)) (reify (eval B η))
eval (^ x)     η = reflect (^ x)
eval (con c)   η = con (eval c η)
eval (SOP Tss) η = SOP (eval-VecList Tss η)

eval-List [] η = []
eval-List (x ∷ xs) η = eval x η ∷ eval-List xs η
eval-VecList [] η = []
eval-VecList (Ts ∷ Tss) η = eval-List Ts η ∷ eval-VecList Tss η
```

Identity environment

```
idEnv : ∀ Φ → Env Φ Φ
idEnv Φ = reflect ∘ `
```

Normalisating a term yields a normal form. We evaluate in the identity
environment to yield a value in the same context as the original term
and then reify to yield a normal form

```
nf : ∀{Φ K} → Φ ⊢⋆ K → Φ ⊢Nf⋆ K
nf t = reify (eval t (idEnv _))

nf-VecList :  ∀{Φ K n} → Vec (List (Φ ⊢⋆ K)) n → Vec (List (Φ ⊢Nf⋆ K)) n
nf-VecList Tss =  vmap (map reify) (eval-VecList Tss (idEnv _))
```

Some properties relating uses of lookup on VecList-functions with List-functions

```
module _ where

  open import Data.Fin using (Fin;zero;suc)
  open import Data.Vec using (lookup)
  open import Relation.Binary.PropositionalEquality using (_≡_;refl; cong; cong₂)

  
  lookup-eval-VecList : ∀ {Φ Ψ n}
              → (e : Fin n)
              → (Tss : Vec (List (Ψ ⊢⋆ *)) n)
              → (η : Env Ψ Φ)
                --------------------------------------------
              → lookup (eval-VecList Tss η) e ≡ eval-List (lookup Tss e) η
  lookup-eval-VecList zero (_ ∷ _) η = refl
  lookup-eval-VecList (suc e) (_ ∷ Tss) η = lookup-eval-VecList e Tss η
```
