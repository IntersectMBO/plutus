\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec hiding (map;_>>=_)
open import Data.List hiding (map)
open import Data.Sum
open import Relation.Nullary
open import Data.Empty

-- we cannot use the standard library's Maybe as it is not set up to
-- compile the Haskell's Maybe and compile pragmas have to go in the
-- same module as defintions

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

{-# COMPILE GHC Maybe = data Maybe (Just | Nothing) #-}

maybe : {A B : Set} → (A → B) → B → Maybe A → B 
maybe f b (just a) = f a
maybe f b nothing  = b

mbind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
mbind (just a) f = f a
mbind nothing  f = nothing

{-# COMPILE GHC mbind = \_ _ a f -> a >>= f #-}

-- the same applies to sums...

data Either (A B : Set) : Set where
  inj₁ : A → Either A B
  inj₂ : B → Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}


eitherBind : ∀{A B E} → Either E A → (A → Either E B) → Either E B
eitherBind (inj₁ e) f = inj₁ e
eitherBind (inj₂ a) f = f a

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

+-monoʳ-≤‴ : (n₁ : ℕ) {x y : ℕ} → x ≤‴ y → n₁ + x ≤‴ n₁ + y
+-monoʳ-≤‴ n p = ≤″⇒≤‴ (≤⇒≤″ (+-monoʳ-≤ n (≤″⇒≤ (≤‴⇒≤″ p))))

_:<_ : ∀{A : Set}{n} → Vec A n → A → Vec A (suc n)
[]        :< a = a ∷ []
(a' ∷ as) :< a = a' ∷ (as :< a)

_:<L_ : ∀{A : Set} → List A → A → List A
[]        :<L a = a ∷ []
(a' ∷ as) :<L a = a' ∷ (as :<L a)

-- Monads

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀{A} → A → F A
    _>>=_   : ∀{A B} → F A → (A → F B) → F B
    
  _>>_ : ∀{A B} → F A → F B → F B
  as >> bs = as >>= const bs

  fmap : ∀{A B} → (A → B) → F A → F B
  fmap f as = as >>= (return ∘ f)

open Monad {{...}} public

instance
  MaybeMonad : Monad Maybe
  MaybeMonad = record { return = just ; _>>=_ = mbind }

sumBind : {A B C : Set} → A ⊎ C → (A → B ⊎ C) → B ⊎ C
sumBind (inj₁ a) f = f a
sumBind (inj₂ c) f = inj₂ c

SumMonad : (C : Set) → Monad (_⊎ C)
SumMonad A = record { return = inj₁ ; _>>=_ = sumBind }

EitherMonad : (E : Set) → Monad (Either E)
EitherMonad E = record { return = inj₂ ; _>>=_ = eitherBind }

data Error : Set where
  typeError : Error
  kindEqError : Error
  notTypeError : Error
  notFunction : Error
  notPiError : Error
  notPat : Error
  nameError : Error
  typeEqError : Error
  typeVarEqError : Error
  tyConError : Error
  builtinError : Error
  unwrapError : Error
  parseError : Error
  scopeError : Error
  gasError : Error

-- the haskell version of Error is defined in Raw
{-# FOREIGN GHC import Raw #-}

{-# COMPILE GHC Error = data Error (TypeError | KindEqError | NotTypeError | NotFunction | NotPiError | NotPat | NameError | TypeEqError | TypeVarEqError | TyConError | BuiltinError | UnwrapError | ParseError | ScopeError | GasError) #-}

instance
  EitherErrorMonad : Monad (Either Error)
  EitherErrorMonad = EitherMonad Error

\end{code}
