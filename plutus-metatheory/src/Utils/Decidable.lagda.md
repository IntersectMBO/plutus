
```
module Utils.Decidable where
```

## Imports

```
open import Data.Bool using (false;true)
open import Function using (const;_∘_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;cong₂;subst)
open import Relation.Nullary using (Dec;yes;no;¬_)
open import Data.Product using (Σ;_×_;proj₁;proj₂) renaming (_,_ to _,,_)
```

Some functions to help define `DecidableEquality` predicates, inspired by effectfully's Generic Library.


```
dmap : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → (¬ A → ¬ B) → Dec A → Dec B
dmap f g (no ¬p) = no (g ¬p)
dmap f g (yes p) = yes (f p)

dcong : ∀ {α β} {A : Set α} {B : Set β} {x y}
      → (f : A → B) → (f x ≡ f y → x ≡ y) → Dec (x ≡ y) → Dec (f x ≡ f y)
dcong f inj = dmap (cong f) (_∘ inj)

dcong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
       → (f : A → B → C)
       → (f x₁ y₁ ≡ f x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂)
       → Dec (x₁ ≡ x₂)
       → Dec (y₁ ≡ y₂)
       → Dec (f x₁ y₁ ≡ f x₂ y₂)
dcong₂ f inj (yes refl) (yes refl) = yes refl
dcong₂ f inj (yes _) (no ¬q) = no (λ x → ¬q (proj₂ (inj x))) 
dcong₂ f inj (no ¬p) _ = no (λ x → ¬p (proj₁ (inj x)))

dhcong : ∀ {α β γ} {A : Set α} {B : A → Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
        → (f : ∀ x → B x → C)
        → (f x₁ y₁ ≡ f x₂ y₂ → Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂))
        → Dec (x₁ ≡ x₂)
        → (∀ y₂ → Dec (y₁ ≡ y₂))
        → Dec (f x₁ y₁ ≡ f x₂ y₂)
dhcong f inj (yes refl) q = dcong (f _) ((λ { (refl ,, yy) → yy }) ∘ inj) (q _)
dhcong f inj (no  c)    q = no λ {p → c (proj₁ (inj p))}

dhcong₂ : ∀ {α β γ} {A : Set α} {B B' : A → Set β} {C : Set γ} {x₁ x₂ y₁ y₂ z₁ z₂}
        → (f : ∀ x → B x → B' x → C)
        → (f x₁ y₁ z₁ ≡ f x₂ y₂ z₂ → Σ (x₁ ≡ x₂) (λ p → subst B p y₁ ≡ y₂ × subst B' p z₁ ≡ z₂ ))
        → Dec (x₁ ≡ x₂)
        → (∀ y₂ → Dec (y₁ ≡ y₂))
        → (∀ z₂ → Dec (z₁ ≡ z₂))
        → Dec (f x₁ y₁ z₁ ≡ f x₂ y₂ z₂)
dhcong₂ f inj (yes refl) qy qz = dcong₂ (f _) ((λ { (refl ,, yy) → yy }) ∘ inj) (qy _) (qz _)
dhcong₂ f inj (no  c)    _  _  = no λ {p → c (proj₁ (inj p))}
```