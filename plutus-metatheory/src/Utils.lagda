
\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans)
open import Function using (const;_∘_)
open import Data.Nat using (ℕ;zero;suc;_≤‴_;_≤_;_+_)
open _≤_
open _≤‴_
open import Data.Nat.Properties using (≤⇒≤″;≤″⇒≤;≤″⇒≤‴;≤‴⇒≤″;+-monoʳ-≤)
                                using (+-suc;m+1+n≢m;+-cancelˡ-≡;m≢1+n+m;m+1+n≢0;+-cancelʳ-≡;+-assoc;+-comm;+-identityʳ)
open import Relation.Binary using (Decidable)
import Data.Integer as I
open import Data.List using (List;[];_∷_;length)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Nullary using (Dec;yes;no;¬_)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Product using (Σ;_×_) renaming (_,_ to _,,_)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Bool using (Bool)


-- we cannot use the standard library's Maybe as it is not set up to
-- compile the Haskell's Maybe and compile pragmas have to go in the
-- same module as definitions

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

case : {A B C : Set} → Either A B → (A → C) → (B → C) → C
case (inj₁ a) f g = f a
case (inj₂ b) f g = g b

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

_I>?_ : Decidable I._>_
i I>? j = j I.<? i

_I≥?_ : Decidable I._≥_
i I≥? j = j I.≤? i

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

{-# FOREIGN GHC import Raw #-}

data RuntimeError : Set where
  gasError : RuntimeError
  userError : RuntimeError
  runtimeTypeError : RuntimeError

{-# COMPILE GHC RuntimeError = data RuntimeError (GasError | UserError | RuntimeTypeError) #-}

postulate ByteString : Set
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}

data DATA : Set where
  iDATA : I.ℤ → DATA
  bDATA : ByteString → DATA

{-# FOREIGN GHC import PlutusCore.Data #-}
{-# COMPILE GHC DATA = data Data (I | B)   #-}

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
  _⇒_ : Kind → Kind → Kind -- function kind

{-# FOREIGN GHC import PlutusCore                       #-}
{-# FOREIGN GHC {-# LANGUAGE GADTs, PatternSynonyms #-} #-}
{-# FOREIGN GHC type KIND = Kind ()                     #-}
{-# FOREIGN GHC pattern Star    = Type ()               #-}
{-# FOREIGN GHC pattern Arrow k j = KindArrow () k j    #-}
{-# COMPILE GHC Kind = data KIND (Star | Arrow)         #-}
\end{code}

Let `I`, `J`, `K` range over kinds:
\begin{code}
variable
  I J K : Kind
\end{code}
## Term constants

Defined separately here rather than using generic version used in the
typed syntax.

\begin{code}
data TermCon : Set where
 integer              : ℤ → TermCon
 bytestring           : ByteString → TermCon
 string               : String → TermCon
 bool                 : Bool → TermCon
 unit                 : TermCon
 pdata                : DATA → TermCon
 bls12-381-g1-element : Bls12-381-G1-Element → TermCon
 bls12-381-g2-element : Bls12-381-G2-Element → TermCon
 bls12-381-mlresult   : Bls12-381-MlResult → TermCon

{-# FOREIGN GHC type TermCon = Some (ValueOf DefaultUni)               #-}
{-# FOREIGN GHC pattern TmInteger    i = Some (ValueOf DefaultUniInteger i) #-}
{-# FOREIGN GHC pattern TmByteString b = Some (ValueOf DefaultUniByteString b) #-}
{-# FOREIGN GHC pattern TmString     s = Some (ValueOf DefaultUniString s) #-}
{-# FOREIGN GHC pattern TmUnit         = Some (ValueOf DefaultUniUnit ()) #-}
{-# FOREIGN GHC pattern TmBool       b = Some (ValueOf DefaultUniBool b) #-}
{-# FOREIGN GHC pattern TmData       d = Some (ValueOf DefaultUniData d) #-}
{-# FOREIGN GHC pattern TmG1Elt      e = Some (ValueOf DefaultUniBLS12_381_G1_Element e) #-}
{-# FOREIGN GHC pattern TmG2Elt      e = Some (ValueOf DefaultUniBLS12_381_G2_Element e) #-}
{-# FOREIGN GHC pattern TmMlResult   r = Some (ValueOf DefaultUniBLS12_381_MlResult r) #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData | TmG1Elt | TmG2Elt | TmMlResult) #-}
\end{code}
