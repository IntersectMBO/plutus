```
module Type.BetaNormal.Equality where
```

```
open import Type
open import Type.Equality
open import Type.BetaNormal
open import Relation.Binary.PropositionalEquality
```

```
data _≡Ne_ {Φ} : ∀{J} → Φ ⊢Ne⋆ J → Φ ⊢Ne⋆ J → Set

data _≡Nf_ {Φ} : ∀{J} → Φ ⊢Nf⋆ J → Φ ⊢Nf⋆ J → Set where
  
  -- congruence rules
 
  ⇒≡Nf : {A A' B B' : Φ ⊢Nf⋆ *}
    → A ≡Nf A'
    → B ≡Nf B'
      ---------------------
    → (A ⇒ B) ≡Nf (A' ⇒ B')
    
  Π≡Nf : ∀{J}{B B' : Φ ,⋆ J ⊢Nf⋆ *}{x}{x'}
    → B ≡Nf B'
      -----------------
    → Π x B ≡Nf Π x' B'
    
  ƛ≡Nf : ∀{K J}{B B' : Φ ,⋆ J ⊢Nf⋆ K}{x}{x'}
    → B ≡Nf B'
      ----------------
    → ƛ x B ≡Nf ƛ x' B'

  con≡Nf : ∀ {tcn} → con tcn ≡Nf con tcn

  ne≡Nf : ∀{K}{A A' : Φ ⊢Ne⋆ K}
    → A ≡Ne A'
      --------------
    → ne A ≡Nf ne A'

data _≡Ne_ {Φ} where
  var≡Ne : ∀{K}{α α' : Φ ∋⋆ K}
    → α ≡ α'
    → ` α ≡Ne ` α'

  ·≡Ne : ∀{K J}{A A' : Φ ⊢Ne⋆ K ⇒ J}{B B' : Φ ⊢Nf⋆ K}
    → A ≡Ne A'
    → B ≡Nf B'
      ---------------------
    → (A · B) ≡Ne (A' · B')

  μ≡Ne : ∀{K} → μ1 {K = K} ≡Ne μ1
```

```
symNf : ∀{Φ J}{A A' : Φ ⊢Nf⋆ J} → A ≡Nf A' → A' ≡Nf A
symNe : ∀{Φ J}{A A' : Φ ⊢Ne⋆ J} → A ≡Ne A' → A' ≡Ne A

symNf (⇒≡Nf p q) = ⇒≡Nf (symNf p) (symNf q)
symNf (Π≡Nf p)   = Π≡Nf (symNf p)
symNf (ƛ≡Nf p)   = ƛ≡Nf (symNf p)
symNf (ne≡Nf p)  = ne≡Nf (symNe p)
symNf con≡Nf     = con≡Nf

symNe (var≡Ne p) = var≡Ne (sym p)
symNe (·≡Ne p q) = ·≡Ne (symNe p) (symNf q)
symNe μ≡Ne       = μ≡Ne
```

```
transNf : ∀{Φ J}{A A' A'' : Φ ⊢Nf⋆ J} → A ≡Nf A' → A' ≡Nf A'' → A ≡Nf A''
transNe : ∀{Φ J}{A A' A'' : Φ ⊢Ne⋆ J} → A ≡Ne A' → A' ≡Ne A'' → A ≡Ne A''

transNf (⇒≡Nf p q) (⇒≡Nf p' q') = ⇒≡Nf (transNf p p') (transNf q q')
transNf (Π≡Nf p)   (Π≡Nf p')    = Π≡Nf (transNf p p')
transNf (ƛ≡Nf p)   (ƛ≡Nf p')    = ƛ≡Nf (transNf p p')
transNf (ne≡Nf p)  (ne≡Nf p')   = ne≡Nf (transNe p p')
transNf con≡Nf     con≡Nf       = con≡Nf

transNe (var≡Ne p) (var≡Ne p')  = var≡Ne (trans p p')
transNe (·≡Ne p q) (·≡Ne p' q') = ·≡Ne (transNe p p') (transNf q q')
transNe μ≡Ne       μ≡Ne         = μ≡Ne
```

```
reflNf : ∀{Φ J}{A : Φ ⊢Nf⋆ J} → A ≡Nf A
reflNe : ∀{Φ J}{A : Φ ⊢Ne⋆ J} → A ≡Ne A

reflNf {A = Π x A} = Π≡Nf reflNf
reflNf {A = A ⇒ B} = ⇒≡Nf reflNf reflNf
reflNf {A = ƛ x A} = ƛ≡Nf reflNf
reflNf {A = ne A}  = ne≡Nf reflNe
reflNf {A = con c} = con≡Nf

reflNe {A = ` α}   = var≡Ne refl
reflNe {A = A · B} = ·≡Ne reflNe reflNf
reflNe {A = μ1}    = μ≡Ne
```

```
open import Type.RenamingSubstitution
renNe-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}{A A' : Φ ⊢Ne⋆ K}
  → A ≡Ne A'
    -------------------------
  → renNe f A ≡Ne renNe g A'

renNf-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}{A A' : Φ ⊢Nf⋆ K}
  → A ≡Nf A'
    ---------------------------
  → renNf f A ≡Nf renNf g A'
renNf-cong p (⇒≡Nf q r) = ⇒≡Nf (renNf-cong p q) (renNf-cong p r)
renNf-cong p (Π≡Nf q)   = Π≡Nf (renNf-cong (ext-cong p) q)
renNf-cong p (ƛ≡Nf q)   = ƛ≡Nf (renNf-cong (ext-cong p) q)
renNf-cong p con≡Nf     = con≡Nf
renNf-cong p (ne≡Nf q)  = ne≡Nf (renNe-cong p q)

renNe-cong p (var≡Ne refl) = var≡Ne (p _)
renNe-cong p (·≡Ne q r) = ·≡Ne (renNe-cong p q) (renNf-cong p r)
renNe-cong p μ≡Ne = μ≡Ne
```

```
open import Function
renNf-id : ∀ {Φ}
  → ∀ {J}
  → (n : Φ ⊢Nf⋆ J)
    -----------------
  → renNf id n ≡Nf n

renNe-id : ∀ {Φ}
  → ∀ {J}
  → (n : Φ ⊢Ne⋆ J)
    ------------------
  → renNe id n ≡Ne n

renNf-id (Π x A)   = Π≡Nf (transNf (renNf-cong ext-id reflNf) (renNf-id A))
renNf-id (A ⇒ A')  = ⇒≡Nf (renNf-id A) (renNf-id A')
renNf-id (ƛ x A)   = ƛ≡Nf (transNf (renNf-cong ext-id reflNf) (renNf-id A))
renNf-id (ne A)    = ne≡Nf (renNe-id A)
renNf-id (con tcn) = con≡Nf

renNe-id (` α)   = var≡Ne refl
renNe-id (A · B) = ·≡Ne (renNe-id A) (renNf-id B)
renNe-id μ1      = μ≡Ne
```

```
renNf-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -------------------------------------------
  → renNf (f ∘ g) A ≡Nf renNf f (renNf g A)
renNe-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢Ne⋆ J)
    -------------------------------------------
  → renNe (f ∘ g) A ≡Ne renNe f (renNe g A)

renNf-comp (Π x B)     = 
  Π≡Nf (transNf (renNf-cong ext-comp reflNf) (renNf-comp B))
renNf-comp (A ⇒ B)     = ⇒≡Nf (renNf-comp A) (renNf-comp B)
renNf-comp (ƛ x A)     =
  ƛ≡Nf (transNf (renNf-cong ext-comp reflNf) (renNf-comp A))
renNf-comp (ne A)      = ne≡Nf (renNe-comp A)
renNf-comp (con tcn)   = con≡Nf

renNe-comp (` x)   = var≡Ne refl
renNe-comp (A · B) = ·≡Ne (renNe-comp A) (renNf-comp B)
renNe-comp μ1      = μ≡Ne
```

```
embNf-cong : ∀{Φ K}{A A' : Φ ⊢Nf⋆ K} → A ≡Nf A' → embNf A ≡α embNf A'
embNe-cong : ∀{Φ K}{A A' : Φ ⊢Ne⋆ K} → A ≡Ne A' → embNe A ≡α embNe A'

embNf-cong (⇒≡Nf p q) = ⇒≡α (embNf-cong p) (embNf-cong q)
embNf-cong (Π≡Nf p)   = Π≡α (embNf-cong p)
embNf-cong (ƛ≡Nf p)   = ƛ≡α (embNf-cong p)
embNf-cong con≡Nf     = con≡α
embNf-cong (ne≡Nf p)  = embNe-cong p

embNe-cong (var≡Ne p) = var≡α p
embNe-cong (·≡Ne p q) = ·≡α (embNe-cong p) (embNf-cong q)
embNe-cong μ≡Ne       = μ≡α
```
