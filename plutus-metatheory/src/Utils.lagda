
\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans;cong₂;subst)
open import Function using (const;_∘_)
open import Data.Nat using (ℕ;zero;suc;_≤‴_;_≤_;_+_)
open _≤_
open _≤‴_
open import Data.Nat.Properties
               using (+-suc;m+1+n≢m;+-cancelˡ-≡;m≢1+n+m;m+1+n≢0;+-cancelʳ-≡;+-assoc;+-comm;+-identityʳ)
open import Relation.Binary using (Decidable)
import Data.Integer as I
import Data.List as L
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Nullary using (Dec;yes;no;¬_)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing; maybe) 
                           renaming (_>>=_ to mbind) public

{-# FOREIGN GHC import Raw #-}

-- we cannot use the standard library's Either as it is not set up to
-- compile the Haskell's Either and compile pragmas have to go in the
-- same module as definitions

data Either (A B : Set) : Set where
  inj₁ : A → Either A B
  inj₂ : B → Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

either : {A B C : Set} → Either A B → (A → C) → (B → C) → C
either (inj₁ a) f g = f a
either (inj₂ b) f g = g b

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

≡-subst-removable : ∀ {a p} {A : Set a}
                    (P : A → Set p) {x y} (p q : x ≡ y) z →
                    subst P p z ≡ subst P q z
≡-subst-removable P refl refl z = refl 
 \end{code}

The type `n ∔ n' ≡ m` 
allows to take two naturals `n` and `n'` such that they sum m.
It is helpful when one wants to do `m` things, while keeping track
of the number of done things (`n`) and things to do (`n'`).
\begin{code}

data _∔_≣_ : ℕ → ℕ → ℕ → Set where
  start : (n : ℕ) →  0 ∔ n ≣ n
  bubble : ∀{n n' m : ℕ} → n ∔ suc n' ≣ m → suc n ∔ n' ≣ m

unique∔ : ∀{n n' m : ℕ}(p p' : n ∔ n' ≣ m) → p ≡ p'
unique∔ (start _) (start _) = refl
unique∔ (bubble p) (bubble p') = cong bubble (unique∔ p p')


+2∔ : ∀(n m t : ℕ) → n + m ≡ t → n ∔ m ≣ t
+2∔ zero m .(zero + m) refl = start _
+2∔ (suc n) m t p = bubble (+2∔ n (suc m) t (trans (+-suc n m) p))

∔2+ : ∀{n m t : ℕ} → n ∔ m ≣ t  → n + m ≡ t 
∔2+ (start _) = refl
∔2+ (bubble bt) = trans (sym (+-suc _ _)) (∔2+ bt)

alldone : ∀(n : ℕ) → n ∔ zero ≣ n
alldone n = +2∔ n 0 n (+-identityʳ n)

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

-- one instance to rule them all...
instance
  EitherP : {A : Set} → Monad (Either A)
  Monad.return EitherP = inj₂
  Monad._>>=_ EitherP  = eitherBind

withE : {A B C : Set} → (A → B) → Either A C → Either B C
withE f (inj₁ a) = inj₁ (f a)
withE f (inj₂ c) = inj₂ c

dec2Either : {A : Set} → Dec A → Either (¬ A) A
dec2Either (yes p) = inj₂ p
dec2Either (no ¬p) = inj₁ ¬p

data RuntimeError : Set where
  gasError : RuntimeError
  userError : RuntimeError
  runtimeTypeError : RuntimeError

{-# COMPILE GHC RuntimeError = data RuntimeError (GasError | UserError | RuntimeTypeError) #-}

postulate ByteString : Set
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}


data _×_ (A B : Set) : Set where
 _,_ : A → B → A × B

{-# FOREIGN GHC type Pair a b = (a , b) #-}
{-# COMPILE GHC _×_ = data Pair ((,))  #-}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : ∀ {A} → List A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

map : ∀{A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

toList : ∀{A} →  List A → L.List A
toList [] = L.[]
toList (x ∷ xs) = x L.∷ toList xs

fromList : ∀{A} →  L.List A → List A
fromList L.[] = []
fromList (x L.∷ xs) = x ∷ fromList xs

map-cong : ∀{A B : Set}{xs : L.List A}{f g : A → B}
     → (∀ x → f x ≡ g x) 
     → L.map f xs ≡ L.map g xs 
map-cong {xs = L.[]} p = refl
map-cong {xs = x L.∷ xs} p = cong₂ L._∷_ (p x) (map-cong p)

infixr 5 _∷_

{-# COMPILE GHC List = data [] ([] | (:)) #-}


data DATA : Set where
  ConstrDATA :  I.ℤ → List DATA → DATA
  MapDATA : List (DATA × DATA) → DATA
  ListDATA : List DATA → DATA
  iDATA : I.ℤ → DATA
  bDATA : ByteString → DATA

{-# FOREIGN GHC import PlutusCore.Data as D #-}
{-# COMPILE GHC DATA = data Data (D.Constr | D.Map | D.List | D.I | D.B)   #-}

postulate eqDATA : DATA → DATA → Bool 
{-# COMPILE GHC eqDATA = (==) #-}

postulate Bls12-381-G1-Element : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.G1 as G1 #-}
{-# COMPILE GHC Bls12-381-G1-Element = type G1.Element #-}

postulate Bls12-381-G2-Element : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.G2 as G2 #-}
{-# COMPILE GHC Bls12-381-G2-Element = type G2.Element #-}

postulate Bls12-381-MlResult : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.Pairing as Pairing #-}
{-# COMPILE GHC Bls12-381-MlResult = type Pairing.MlResult #-}
\end{code}

Kinds

The kind of types is `*`. Plutus core core is based on System Fω which
is higher order so we have `⇒` for type level functions. We also have
a kind called `#` which is used for sized integers and bytestrings.

\begin{code}
data Kind : Set where
  *   : Kind               -- type
  ♯   : Kind               -- builtin
  _⇒_ : Kind → Kind → Kind -- function kind

{-# COMPILE GHC Kind = data KIND (Star | Sharp | Arrow )         #-}
\end{code}

Let `I`, `J`, `K` range over kinds:
\begin{code}
variable
  I J K : Kind
\end{code}
 