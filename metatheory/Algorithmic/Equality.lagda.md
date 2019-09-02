```
module Algorithmic.Equality where
```

```
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
```

```
data Eq : ∀{Φ}{A A' : Φ ⊢Nf⋆ *} → A ≡Nf A' → ∀{Γ} → Γ ⊢ A → Γ ⊢ A' → Set where
  
```

```
postulate
  coh : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}(p : A ≡Nf A'){Γ}(t : Γ ⊢ A) → Eq p t (conv⊢ reflCtx p t)
```
