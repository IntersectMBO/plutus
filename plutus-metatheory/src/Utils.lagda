
\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans)
open import Function using (const;_∘_)
open import Data.Nat using (ℕ;zero;suc;_≤‴_;_≤_;_+_)
open _≤_
open _≤‴_
open import Data.Nat.Properties
               using (+-suc;m+1+n≢m;+-cancelˡ-≡;m≢1+n+m;m+1+n≢0;+-cancelʳ-≡;+-assoc;+-comm;+-identityʳ)
open import Relation.Binary using (Decidable)
import Data.Integer as I
import Data.List using (List)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Relation.Nullary using (Dec;yes;no;¬_)
open import Data.Empty using (⊥;⊥-elim)
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

{-# FOREIGN GHC import Raw #-}

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

infixr 5 _∷_

{-# COMPILE GHC List = data [] ([] | (:)) #-}


data DATA : Set where
  ConstrDATA :  I.ℤ → List DATA → DATA
  MapDATA : List (DATA × DATA) → DATA
  ListDATA : List DATA → DATA
  iDATA : I.ℤ → DATA
  bDATA : ByteString → DATA

{-# FOREIGN GHC import PlutusCore.Data #-}
{-# COMPILE GHC DATA = data Data (Constr | Map | List | I | B)   #-}

postulate eqDATA : DATA → DATA → Bool 
{-# COMPILE GHC eqDATA = (==) #-}

data AtomicTyCon : Set where
  integer    : AtomicTyCon
  bytestring : AtomicTyCon 
  string     : AtomicTyCon 
  unit       : AtomicTyCon 
  bool       : AtomicTyCon
  pdata      : AtomicTyCon 

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC AtomicTyCon = data AtomicTyCon (ATyConInt | ATyConBS | ATyConStr | ATyConUnit | ATyConBool | ATyConData) #-}

decAtomicTyCon : (c c' : AtomicTyCon) → Dec (c ≡ c')
decAtomicTyCon integer integer = yes refl
decAtomicTyCon integer bytestring = no λ()
decAtomicTyCon integer string = no λ()
decAtomicTyCon integer unit = no λ()
decAtomicTyCon integer bool = no λ()
decAtomicTyCon integer pdata = no λ()
decAtomicTyCon bytestring integer = no λ()
decAtomicTyCon bytestring bytestring = yes refl
decAtomicTyCon bytestring string = no λ()
decAtomicTyCon bytestring unit = no λ()
decAtomicTyCon bytestring bool = no λ()
decAtomicTyCon bytestring pdata = no λ()
decAtomicTyCon string integer = no λ()
decAtomicTyCon string bytestring = no λ()
decAtomicTyCon string string = yes refl
decAtomicTyCon string unit = no λ()
decAtomicTyCon string bool = no λ()
decAtomicTyCon string pdata = no λ()
decAtomicTyCon unit integer = no λ()
decAtomicTyCon unit bytestring = no λ()
decAtomicTyCon unit string = no λ()
decAtomicTyCon unit unit = yes refl
decAtomicTyCon unit bool = no λ()
decAtomicTyCon unit pdata = no λ()
decAtomicTyCon bool integer = no λ()
decAtomicTyCon bool bytestring = no λ()
decAtomicTyCon bool string = no λ()
decAtomicTyCon bool unit = no λ()
decAtomicTyCon bool bool = yes refl
decAtomicTyCon bool pdata = no λ()
decAtomicTyCon pdata integer = no λ()
decAtomicTyCon pdata bytestring = no λ()
decAtomicTyCon pdata string = no λ()
decAtomicTyCon pdata unit = no λ()
decAtomicTyCon pdata bool = no λ()
decAtomicTyCon pdata pdata = yes refl
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
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  unit       : TermCon
  pdata      : DATA → TermCon
  pairDATA   : DATA → DATA → TermCon
  pairID     : ℤ → List DATA → TermCon 
  listData   : List DATA → TermCon
  listPair   : List (DATA × DATA) → TermCon


{-# FOREIGN GHC type TermCon = Some (ValueOf DefaultUni) #-}
{-# FOREIGN GHC pattern TmInteger    i = Some (ValueOf DefaultUniInteger i) #-}
{-# FOREIGN GHC pattern TmByteString b = Some (ValueOf DefaultUniByteString b) #-}
{-# FOREIGN GHC pattern TmString     s = Some (ValueOf DefaultUniString s) #-}
{-# FOREIGN GHC pattern TmUnit         = Some (ValueOf DefaultUniUnit ()) #-}
{-# FOREIGN GHC pattern TmBool       b = Some (ValueOf DefaultUniBool b) #-}
{-# FOREIGN GHC pattern TmData       d = Some (ValueOf DefaultUniData d) #-}
{-# FOREIGN GHC pattern TmPairData a b = Some (ValueOf (DefaultUniPair DefaultUniData DefaultUniData) (a,b)) #-}
{-# FOREIGN GHC pattern TmPairID   a b = Some (ValueOf (DefaultUniPair DefaultUniInteger (DefaultUniList DefaultUniData)) (a,b)) #-}
{-# FOREIGN GHC pattern TmListData  xs = Some (ValueOf (DefaultUniList DefaultUniData) xs) #-}
{-# FOREIGN GHC pattern TmListPair  xs = Some (ValueOf (DefaultUniList (DefaultUniPair DefaultUniData DefaultUniData)) xs) #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData | TmPairData | TmPairID | TmListData | TmListPair) #-}
\end{code}
