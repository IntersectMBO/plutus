\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

{-# COMPILE GHC Maybe = data Maybe (Just | Nothing) #-}

maybe : {A B : Set} → (A → B) → B → Maybe A → B
maybe f b (just a) = f a
maybe f b nothing  = b

map : {A B : Set} → (A → B) → Maybe A → Maybe B
map f (just a) = just (f a)
map f nothing  = nothing

open import Relation.Nullary
open import Data.Empty

decIf : ∀{A B : Set} → Dec A → B → B → B
decIf (yes p) t f = t
decIf (no ¬p) t f = f

cong₃ : {A B C D : Set} → (f : A → B → C → D)
  → {a a' : A} → a ≡ a'
  → {b b' : B} → b ≡ b'
  → {c c' : C} → c ≡ c'
  → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

z≤‴n : ∀ {n} → zero  ≤‴ n
z≤‴n {n} = ≤″⇒≤‴ (≤⇒≤″ z≤n)

lem¬≤ : ∀{n} → ¬ (suc n Data.Nat.≤ n)
lem¬≤ (s≤s p) = lem¬≤ p

lem≤‴ : ∀{m n}(p q : m ≤‴ n) → p ≡ q
lem≤‴ ≤‴-refl ≤‴-refl     = refl
lem≤‴ ≤‴-refl (≤‴-step q) = ⊥-elim (lem¬≤ (≤″⇒≤ (≤‴⇒≤″ q)))
lem≤‴ (≤‴-step p) ≤‴-refl = ⊥-elim (lem¬≤ (≤″⇒≤ (≤‴⇒≤″ p)))
lem≤‴ (≤‴-step p) (≤‴-step q) = cong ≤‴-step (lem≤‴ p q)

open import Data.Vec
open import Data.List

_:<_ : ∀{A : Set}{n} → Vec A n → A → Vec A (suc n)
[]        :< a = a ∷ []
(a' ∷ as) :< a = a' ∷ (as :< a)

_:<L_ : ∀{A : Set} → List A → A → List A
[]        :<L a = a ∷ []
(a' ∷ as) :<L a = a' ∷ (as :<L a)

\end{code}
