```
module Type.BetaNormal.Equality where
```

```
open import Type
open import Type.BetaNormal
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
    → ` α ≡Ne ` α' 

  ·≡Ne : ∀{K J}{A A' : Φ ⊢Ne⋆ K ⇒ J}{B B' : Φ ⊢Nf⋆ K}
    → A ≡Ne A'
    → B ≡Nf B'
      ---------------------
    → (A · B) ≡Ne (A' · B')
```
