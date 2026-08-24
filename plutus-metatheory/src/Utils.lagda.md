---
title: Utils
layout: page
---
```
module Utils where
```
## Imports
```
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans;cong₂;subst)
open import Function using (const;_∘_)
open import Data.Nat using (ℕ;zero;suc;_≤‴_;_≤_;_+_;_<_;_<?_)
open import Data.Fin using (Fin;suc;zero;toℕ;fromℕ<)
open _≤_
open _≤‴_
open import Data.Nat.Properties
               using (+-suc;m+1+n≢m;+-cancelˡ-≡;m≢1+n+m;m+1+n≢0;+-cancelʳ-≡;+-assoc;+-comm;+-identityʳ)
open import Relation.Binary using (Decidable)
import Data.Integer as I
import Data.Integer.Properties
import Data.List as L
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Nullary using (Dec;yes;no;¬_;isYes;map′;_×-dec_)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (ℤ; +_)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; maybe)
                           renaming (_>>=_ to mbind) public
open import Data.Unit using (⊤)
open import Level using (_⊔_)
open import Agda.Builtin.TrustMe using (primTrustMe)

{-# FOREIGN GHC import Raw #-}

```
## Either

We cannot use the standard library's Either as it is not set up to
compile the Haskell's Either and compile pragmas have to go in the
same module as definitions.
```

data Either (A B : Set) : Set where
  inj₁ : A → Either A B
  inj₂ : B → Either A B

{-# COMPILE GHC Either = data Either (Left | Right) #-}

either : {A B C : Set} → Either A B → (A → C) → (B → C) → C
either (inj₁ a) f g = f a
either (inj₂ b) f g = g b

is-inj₁ : ∀ {A B} → Either A B → Bool
is-inj₁ (inj₁ _) = false
is-inj₁ (inj₂ _) = true

is-inj₂ : ∀ {A B} → Either A B → Bool
is-inj₂ (inj₂ _) = true
is-inj₂ (inj₁ _) = false

eitherBind : ∀{A B E} → Either E A → (A → Either E B) → Either E B
eitherBind (inj₁ e) f = inj₁ e
eitherBind (inj₂ a) f = f a

decIf : ∀{A B : Set} → Dec A → B → B → B
decIf (yes p) t f = t
decIf (no ¬p) t f = f

infixr 8 _<|>_

_<|>_ : ∀{A : Set} → Maybe A → Maybe A → Maybe A
nothing <|> m = m
just x <|> _ = just x

maybeToEither : {A B : Set} → A → Maybe B → Either A B
maybeToEither x = maybe inj₂ (inj₁ x)

-- try = flip maybeToEither
try : {A B : Set} → Maybe B → A → Either A B
try m x = maybe inj₂ (inj₁ x) m

eitherToMaybe : ∀ {A B} → Either A B → Maybe B
eitherToMaybe (inj₁ _) = nothing
eitherToMaybe (inj₂ x) = just x

natToFin : {n : ℕ} → ℕ → Maybe (Fin n)
natToFin {n} m with m <? n
... | yes n<m = just (fromℕ< n<m)
... | no _ = nothing

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
 ```
## Natural Sum Type

The type `n ∔ n' ≡ m` takes two naturals `n` and `n'` such that they sum to m.
It is helpful when one wants to do `m` things, while keeping track
of the number of done things (`n`) and things to do (`n'`).
```

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

```
## Monads

This introduces the Monad operators.

```
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

```
# Writer Monad
```

record Writer (M : Set)(A : Set) : Set where
   constructor _,_
   field
     wrvalue : A
     accum : M

module WriterMonad {M : Set}(e : M)(_∙_ : M → M → M) where
  instance
    WriterMonad : Monad (Writer M)
    Monad.return WriterMonad x = x , e
    (WriterMonad Monad.>>= (x , w)) f = let (y , w') = f x in y , (w ∙ w')

  tell : (w : M) → Writer M ⊤
  tell w = _ , w

```
## Errors and ByteStrings

```
data RuntimeError : Set where
  gasError : RuntimeError
  userError : RuntimeError
  runtimeTypeError : RuntimeError

{-# COMPILE GHC RuntimeError = data RuntimeError (GasError | UserError | RuntimeTypeError) #-}

postulate ByteString : Set
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}

postulate
  mkByteString : String → ByteString

eqByteString? : (b₁ b₂ : ByteString) → Dec (b₁ ≡ b₂)
eqByteString? b₁ b₂ with primTrustMe {Agda.Primitive.lzero} {ByteString} {b₁} {b₂}
... | refl = yes refl

```
### Equality of postulated types

`ByteString` (like the BLS12-381 element types and `Value` below) is postulated, so at
type-checking time we may only rely on Agda's unification algorithm to decide equality
of its values. The decision procedures for these types (`eqByteString?`,
`eqBls12-381-G1-Element?`, `eqBls12-381-G2-Element?`, `eqBls12-381-MlResult?`, `eqValue?`)
do this by matching on `primTrustMe`, which reduces to `refl` exactly when the two sides
are definitionally equal.

Let's look at the behavior of `eqByteString? (mkByteString "foo") (mkByteString "foo")` vs
`eqByteString? (mkByteString "foo") (mkByteString "bar")`.

At type-checking time, if the two bytestrings are definitionally equal unification will
succeed, and the function will return `yes refl`.

```
_ : isYes (eqByteString? (mkByteString "") (mkByteString "")) ≡ true
_ = refl
```

There is no way to return `no` because there is no way to prove that the two
terms are not equal without extra information about the `ByteString` type. But
this is enough to make Agda not successfully type-check the program, since it
gets stuck while trying to normalize `primTrustMe`:

```
-- The following does not type check because reduction gets stuck
-- _ : isYes (eqByteString? (mkByteString "foo") (mkByteString "bar")) ≡ false
-- _ = refl
```

So even though these procedures can never produce a negative proof, they are still *safe*
checkers at type-checking time: they either answer `yes` correctly or refuse to reduce.

These decision procedures cannot be used for runtime equality checks: at runtime the
values `≡` depends on are erased and `primTrustMe` is compiled to `refl`, so the compiled
code always takes the `yes` branch. Runtime equality of postulated types instead goes
through Bool-valued wrappers such as `eqByteStringᵇ`, whose `COMPILE GHC` pragma replaces
the Agda definition with Haskell's `(==)` (see also `HsEq` in `Untyped.Equality`).

```

eqByteStringᵇ : ByteString → ByteString → Bool
eqByteStringᵇ b₁ b₂ = isYes (eqByteString? b₁ b₂)
{-# COMPILE GHC eqByteStringᵇ = (==) #-}

```
## Record Types
```

record _×_ (A B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

infixr 4 _,_
infixr 2 _×_

{-# FOREIGN GHC type Pair a b = (a , b) #-}
{-# COMPILE GHC _×_ = data Pair ((,))  #-}

```
## Lists and Maps
```

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data All {l}  {A : Set} (P : A → Set l) : List A → Set l where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

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

-- Implementation of UPLC's dropList builtin
dropLIST : ∀{A} → ℤ → List A → List A
dropLIST (+ n) l = drop n l
  where drop : ∀{A} → ℕ → List A → List A
        drop zero xs = xs
        drop (suc n) [] = []
        drop (suc n) (_ ∷ xs) = drop n xs
dropLIST _ l = l

map-cong : ∀{A B : Set}{xs : L.List A}{f g : A → B}
     → (∀ x → f x ≡ g x)
     → L.map f xs ≡ L.map g xs
map-cong {xs = L.[]} p = refl
map-cong {xs = x L.∷ xs} p = cong₂ L._∷_ (p x) (map-cong p)

infixr 5 _∷_

sequence : ∀ {A M} {{_ : Monad M}} → List (M A) → M (List A)
sequence [] = return []
sequence (mx ∷ mxs) =
    mx >>= λ x →
    sequence mxs >>= λ xs →
    return (x ∷ xs)

mapM : ∀ {A B M} {{_ : Monad M}} → (A → M B) → List A → M (List B)
mapM f = sequence ∘ map f

{-# COMPILE GHC List = data [] ([] | (:)) #-}

```
## Arrays

```

postulate Array : Set → Set
{-# FOREIGN GHC import qualified Data.Vector.Strict as Strict #-}
{-# COMPILE GHC Array = type Strict.Vector #-}

variable A : Set

postulate
  HSlengthOfArray : Array A → ℤ
  HSlistToArray : (ls : List A) → Array A
  HSindexArray : Array A → ℤ → A
-- These have to consume the hidden {A : Set} param in the Agda.
{-# COMPILE GHC HSlengthOfArray = \() -> \as -> toInteger (Strict.length as) #-}
{-# COMPILE GHC HSlistToArray = \() -> Strict.fromList #-}
{-# COMPILE GHC HSindexArray = \() -> \as -> \i -> as Strict.! (fromInteger i) #-}

-- This only exists for literal arrays in certificates,
-- much like mkBytestring above.
postulate
  mkArray : {A : Set} → List A → Array A

```
## DATA
```

data DATA : Set where
  ConstrDATA :  I.ℤ → List DATA → DATA
  MapDATA : List (DATA × DATA) → DATA
  ListDATA : List DATA → DATA
  iDATA : I.ℤ → DATA
  bDATA : ByteString → DATA

{-# FOREIGN GHC import PlutusCore.Data as D #-}
{-# COMPILE GHC DATA = data Data (D.Constr | D.Map | D.List | D.I | D.B)   #-}

eqDATA? : (d₁ d₂ : DATA) → Dec (d₁ ≡ d₂)
eqListDATA? : (l₁ l₂ : List DATA) → Dec (l₁ ≡ l₂)
eqPairDATA? : (p₁ p₂ : DATA × DATA) → Dec (p₁ ≡ p₂)
eqListPairDATA? : (l₁ l₂ : List (DATA × DATA)) → Dec (l₁ ≡ l₂)

eqDATA? (ConstrDATA i₁ l₁) (ConstrDATA i₂ l₂) =
  map′ (λ { (p , q) → cong₂ ConstrDATA p q })
       (λ { refl → refl , refl })
       ((i₁ Data.Integer.Properties.≟ i₂) ×-dec eqListDATA? l₁ l₂)
eqDATA? (ConstrDATA _ _) (MapDATA _) = no λ ()
eqDATA? (ConstrDATA _ _) (ListDATA _) = no λ ()
eqDATA? (ConstrDATA _ _) (iDATA _) = no λ ()
eqDATA? (ConstrDATA _ _) (bDATA _) = no λ ()
eqDATA? (MapDATA _) (ConstrDATA _ _) = no λ ()
eqDATA? (MapDATA m₁) (MapDATA m₂) =
  map′ (cong MapDATA) (λ { refl → refl }) (eqListPairDATA? m₁ m₂)
eqDATA? (MapDATA _) (ListDATA _) = no λ ()
eqDATA? (MapDATA _) (iDATA _) = no λ ()
eqDATA? (MapDATA _) (bDATA _) = no λ ()
eqDATA? (ListDATA _) (ConstrDATA _ _) = no λ ()
eqDATA? (ListDATA _) (MapDATA _) = no λ ()
eqDATA? (ListDATA l₁) (ListDATA l₂) =
  map′ (cong ListDATA) (λ { refl → refl }) (eqListDATA? l₁ l₂)
eqDATA? (ListDATA _) (iDATA _) = no λ ()
eqDATA? (ListDATA _) (bDATA _) = no λ ()
eqDATA? (iDATA _) (ConstrDATA _ _) = no λ ()
eqDATA? (iDATA _) (MapDATA _) = no λ ()
eqDATA? (iDATA _) (ListDATA _) = no λ ()
eqDATA? (iDATA i₁) (iDATA i₂) =
  map′ (cong iDATA) (λ { refl → refl }) (i₁ Data.Integer.Properties.≟ i₂)
eqDATA? (iDATA _) (bDATA _) = no λ ()
eqDATA? (bDATA _) (ConstrDATA _ _) = no λ ()
eqDATA? (bDATA _) (MapDATA _) = no λ ()
eqDATA? (bDATA _) (ListDATA _) = no λ ()
eqDATA? (bDATA _) (iDATA _) = no λ ()
eqDATA? (bDATA b₁) (bDATA b₂) =
  map′ (cong bDATA) (λ { refl → refl }) (eqByteString? b₁ b₂)

eqListDATA? [] [] = yes refl
eqListDATA? [] (_ ∷ _) = no λ ()
eqListDATA? (_ ∷ _) [] = no λ ()
eqListDATA? (x₁ ∷ l₁) (x₂ ∷ l₂) =
  map′ (λ { (p , q) → cong₂ _∷_ p q })
       (λ { refl → refl , refl })
       (eqDATA? x₁ x₂ ×-dec eqListDATA? l₁ l₂)

eqPairDATA? (x₁ , y₁) (x₂ , y₂) =
  map′ (λ { (p , q) → cong₂ _,_ p q })
       (λ { refl → refl , refl })
       (eqDATA? x₁ x₂ ×-dec eqDATA? y₁ y₂)

eqListPairDATA? [] [] = yes refl
eqListPairDATA? [] (_ ∷ _) = no λ ()
eqListPairDATA? (_ ∷ _) [] = no λ ()
eqListPairDATA? (p₁ ∷ l₁) (p₂ ∷ l₂) =
  map′ (λ { (p , q) → cong₂ _∷_ p q })
       (λ { refl → refl , refl })
       (eqPairDATA? p₁ p₂ ×-dec eqListPairDATA? l₁ l₂)

eqDATA : DATA → DATA → Bool
eqDATA d₁ d₂ = isYes (eqDATA? d₁ d₂)
{-# COMPILE GHC eqDATA = (==) #-}

postulate Bls12-381-G1-Element : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.G1 as G1 #-}
{-# COMPILE GHC Bls12-381-G1-Element = type G1.Element #-}

eqBls12-381-G1-Element? : (b₁ b₂ : Bls12-381-G1-Element) → Dec (b₁ ≡ b₂)
eqBls12-381-G1-Element? b₁ b₂ with primTrustMe {Agda.Primitive.lzero} {Bls12-381-G1-Element} {b₁} {b₂}
... | refl = yes refl

eqBls12-381-G1-Elementᵇ : Bls12-381-G1-Element → Bls12-381-G1-Element → Bool
eqBls12-381-G1-Elementᵇ b₁ b₂ = isYes (eqBls12-381-G1-Element? b₁ b₂)
{-# COMPILE GHC eqBls12-381-G1-Elementᵇ = (==) #-}

postulate Bls12-381-G2-Element : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.G2 as G2 #-}
{-# COMPILE GHC Bls12-381-G2-Element = type G2.Element #-}

eqBls12-381-G2-Element? : (b₁ b₂ : Bls12-381-G2-Element) → Dec (b₁ ≡ b₂)
eqBls12-381-G2-Element? b₁ b₂ with primTrustMe {Agda.Primitive.lzero} {Bls12-381-G2-Element} {b₁} {b₂}
... | refl = yes refl

eqBls12-381-G2-Elementᵇ : Bls12-381-G2-Element → Bls12-381-G2-Element → Bool
eqBls12-381-G2-Elementᵇ b₁ b₂ = isYes (eqBls12-381-G2-Element? b₁ b₂)
{-# COMPILE GHC eqBls12-381-G2-Elementᵇ = (==) #-}

postulate Bls12-381-MlResult : Set
{-# FOREIGN GHC import qualified PlutusCore.Crypto.BLS12_381.Pairing as Pairing #-}
{-# COMPILE GHC Bls12-381-MlResult = type Pairing.MlResult #-}

eqBls12-381-MlResult? : (b₁ b₂ : Bls12-381-MlResult) → Dec (b₁ ≡ b₂)
eqBls12-381-MlResult? b₁ b₂ with primTrustMe {Agda.Primitive.lzero} {Bls12-381-MlResult} {b₁} {b₂}
... | refl = yes refl

eqBls12-381-MlResultᵇ : Bls12-381-MlResult → Bls12-381-MlResult → Bool
eqBls12-381-MlResultᵇ b₁ b₂ = isYes (eqBls12-381-MlResult? b₁ b₂)
{-# COMPILE GHC eqBls12-381-MlResultᵇ = (==) #-}
```

## Value

The Value type is currently postulated, but should eventually be implemented,
for example as nested maps. 

```
-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1872)
postulate Value : Set
{-# FOREIGN GHC import qualified PlutusCore.Value as V #-}
{-# COMPILE GHC Value = type V.Value #-}
```

```
eqValue? : (v₁ v₂ : Value) → Dec (v₁ ≡ v₂)
eqValue? v₁ v₂ with primTrustMe {Agda.Primitive.lzero} {Value} {v₁} {v₂}
... | refl = yes refl

eqValueᵇ : Value → Value → Bool
eqValueᵇ v₁ v₂ = isYes (eqValue? v₁ v₂)
{-# COMPILE GHC eqValueᵇ = (==) #-}
```

### Constructing constants of type Value

Since the Value type is postulated, we also postulate a way to construct Value
constants, which is used for printing Value constants when dumping certifier
traces in Haskell (AgdaUnparse).

```
postulate valueFromList : List (ByteString × List (ByteString × ℤ)) → Value
```

An Agda implementation of Value should only have quantities in the interval
-2^127 ... 2^127-1, and must have ordered keys and no duplicated keys (see UPLC
specification pdf for more detail). Therefore, a function like `valueFromList`
would be partial in practice. For the time being, we keep the postulate as a
total function for convenience and because we expect the Haskell code to enforce
these constraints already.

## Kinds

The kind of types is `*`. Plutus core core is based on System Fω which
is higher order so we have `⇒` for type level functions. We also have
a kind called `#` which is used for builtin types.

```
data Kind : Set where
  *   : Kind               -- type
  ♯   : Kind               -- builtin
  _⇒_ : Kind → Kind → Kind -- function kind

{-# COMPILE GHC Kind = data KIND (Star | Sharp | Arrow )         #-}
```

Let `I`, `J`, `K` range over kinds:
```
variable
  I J K : Kind
```
