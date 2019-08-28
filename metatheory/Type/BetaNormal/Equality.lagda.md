```
module Type.BetaNormal.Equality where
```

```
open import Type
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

  ne≡Nf : ∀{K}{A A' : Φ ⊢Ne⋆ K}
    → A ≡Ne A'
      --------------
    → ne A ≡Nf ne A'

data _≡Ne_ {Φ} where
  var≡Ne : ∀{K}{α α' : Φ ∋⋆ K}
    → α ≡ α'
      ------------
    → ` α ≡Ne ` α' 

  ·≡Ne : ∀{K J}{A A' : Φ ⊢Ne⋆ K ⇒ J}{B B' : Φ ⊢Nf⋆ K}
    → A ≡Ne A'
    → B ≡Nf B'
      ---------------------
    → (A · B) ≡Ne (A' · B')
```

```
symNf : ∀{Φ J}{A A' : Φ ⊢Nf⋆ J} → A ≡Nf A' → A' ≡Nf A
symNe : ∀{Φ J}{A A' : Φ ⊢Ne⋆ J} → A ≡Ne A' → A' ≡Ne A

symNf (⇒≡Nf p q) = ⇒≡Nf (symNf p) (symNf q)
symNf (Π≡Nf p)   = Π≡Nf (symNf p)
symNf (ƛ≡Nf p)   = ƛ≡Nf (symNf p)
symNf (ne≡Nf p)  = ne≡Nf (symNe p)

symNe (var≡Ne p) = var≡Ne (sym p)
symNe (·≡Ne p q) = ·≡Ne (symNe p) (symNf q)
```

```
transNf : ∀{Φ J}{A A' A'' : Φ ⊢Nf⋆ J} → A ≡Nf A' → A' ≡Nf A'' → A ≡Nf A''
transNe : ∀{Φ J}{A A' A'' : Φ ⊢Ne⋆ J} → A ≡Ne A' → A' ≡Ne A'' → A ≡Ne A''

transNf (⇒≡Nf p q) (⇒≡Nf p' q') = ⇒≡Nf (transNf p p') (transNf q q')
transNf (Π≡Nf p)   (Π≡Nf p')    = Π≡Nf (transNf p p')
transNf (ƛ≡Nf p)   (ƛ≡Nf p')    = ƛ≡Nf (transNf p p')
transNf (ne≡Nf p)  (ne≡Nf p')   = ne≡Nf (transNe p p')

transNe (var≡Ne p) (var≡Ne p')  = var≡Ne (trans p p')
transNe (·≡Ne p q) (·≡Ne p' q') = ·≡Ne (transNe p p') (transNf q q')
```
