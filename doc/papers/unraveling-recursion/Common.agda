module Common where
  ∗ : Set₁
  ∗ = Set

  _∘_ : {A B C : ∗} → (B → C) → (A → B) → (A → C)
  f ∘ g = λ a → f (g a)

  infixr 2 _×_
  infixr 1 _⊎_

  data _×_ (A B : ∗) : ∗ where
    _,_ : A → B → A × B

  proj₁ : ∀ {A B} → A × B → A
  proj₁ (a , b) = a

  proj₂ : ∀ {A B} → A × B → B
  proj₂ (a , b) = b

  uncurry : {A B C : ∗} → (A → B → C) → (A × B → C)
  uncurry f (a , b) = f a b

  data _⊎_ (A B : ∗) : ∗ where
    inj₁ : (x : A) → A ⊎ B
    inj₂ : (y : B) → A ⊎ B
