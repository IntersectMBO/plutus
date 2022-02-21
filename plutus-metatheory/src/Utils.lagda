
\begin{code}
module Utils where

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary using (Decidable)
import Data.Integer as I
open import Data.Vec hiding (map;_>>=_;_++_)
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

data Bwd (A : Set) : Set where
  [] : Bwd A
  _:<_ : Bwd A → A → Bwd A

infixl 5 _:<_


bwd-length : ∀{A} → Bwd A → ℕ
bwd-length [] = 0
bwd-length (az :< a) = Data.Nat.suc (bwd-length az)

_<>>_ : ∀{A} → Bwd A → List A → List A
[] <>> as = as
(az :< a) <>> as = az <>> (a ∷ as)

_<><_ : ∀{A} → Bwd A → List A → Bwd A
az <>< []       = az
az <>< (a ∷ as) = (az :< a) <>< as

_:<L_ : ∀{A : Set} → List A → A → List A
[]        :<L a = a ∷ []
(a' ∷ as) :<L a = a' ∷ (as :<L a)

data _≤L_ {A : Set} : List A → List A → Set where
 base : ∀{as} → as ≤L as
 skip : ∀{as as' a} → as ≤L as' → as ≤L (a ∷ as')

[]≤L : {A : Set}(as : List A) → [] ≤L as
[]≤L []       = base
[]≤L (a ∷ as) = skip ([]≤L as)

data _≤L'_ {A : Set} : List A → List A → Set where
 base : ∀{as} → as ≤L' as
 skip : ∀{as as' a} → (a ∷ as) ≤L' as' → as ≤L' as'

data _<>>_∈_ : ∀{A} → Bwd A → List A → List A → Set where
  start : ∀{A}(as : List A) → [] <>> as ∈ as
  bubble : ∀{A}{a : A}{as : Bwd A}{as' as'' : List A} → as <>> (a ∷ as') ∈ as''
    → (as :< a) <>> as' ∈ as''

data _<><_∈_ : ∀{A} → Bwd A → List A → Bwd A → Set where
  start : ∀{A}(as : Bwd A) → as <>< [] ∈ as
  bubble : ∀{A}{a : A}{as as'' : Bwd A}{as' : List A}
    → (as :< a) <>< as' ∈ as''
    → as <>< (a ∷ as') ∈ as''

unique<>> : ∀{A}{az : Bwd A}{as as' : List A}(p p' : az <>> as ∈ as') → p ≡ p'
unique<>> (start _) (start _) = refl
unique<>> (bubble p) (bubble p') = cong bubble (unique<>> p p')

_<>>_∈'_ : ∀{A} → Bwd A → List A → List A → Set
xs <>> ys ∈' zs = xs <>> ys ≡ zs

open import Data.Nat.Properties using (+-suc;m+1+n≢m;+-cancelˡ-≡;m≢1+n+m;m+1+n≢0;+-cancelʳ-≡;+-assoc;+-comm)

<>>-length : ∀{A}(az : Bwd A)(as : List A)
  → Data.List.length (az <>> as) ≡ bwd-length az Data.Nat.+ Data.List.length as
<>>-length [] as = refl
<>>-length (az :< x) as = trans (<>>-length az (x ∷ as)) (+-suc _ _)



-- reasoning about the length inspired by similar proof about ++ in the stdlib
<>>-rcancel : ∀{A}(az : Bwd A)(as : List A) → az <>> [] ≡ az <>> as → as ≡ []
<>>-rcancel []       as p = sym p
<>>-rcancel (az :< a) [] p = refl
<>>-rcancel (az :< a) (a' ∷ as) p = ⊥-elim
  (m+1+n≢m 1
           (sym (+-cancelˡ-≡ (bwd-length az)
                             (trans (trans (sym (<>>-length az (a ∷ [])))
                                           (cong Data.List.length p))
                                    (<>>-length az (a ∷ a' ∷ as))))))

<>>-lcancel : ∀{A}(az : Bwd A)(as : List A) → as ≡ az <>> as → az ≡ []
<>>-lcancel []       as p = refl
<>>-lcancel (az :< a) as p = ⊥-elim
  (m≢1+n+m (Data.List.length as)
           (trans (trans (cong Data.List.length p)
                         (<>>-length az (a ∷ as)))
                  (+-suc (bwd-length az) (Data.List.length as))))

open import Data.Product renaming (_,_ to _,,_)

<>>-lcancel' : ∀{A}(az : Bwd A)(as as' : List A)
  → as ≡ az <>> as'
  → Data.List.length as ≡ Data.List.length as'
  → (az ≡ []) × (as ≡ as')
<>>-lcancel' [] as as' p q = refl ,, p
<>>-lcancel' (az :< a) as as' p q = ⊥-elim
  (m≢1+n+m (Data.List.length as')
           (trans (trans (trans (sym q) (cong Data.List.length p))
                         (<>>-length az (a ∷ as')))
                  (+-suc (bwd-length az) (Data.List.length as'))))

<>>2<>>' : ∀{A}(xs : Bwd A)(ys zs : List A) → xs <>> ys ∈ zs → xs <>> ys ∈' zs
<>>2<>>' [] ys .ys (start .ys) = refl
<>>2<>>' (xs :< x) ys zs (bubble p) = <>>2<>>' xs (x ∷ ys) zs p

<>>'2<>> : ∀{A}(xs : Bwd A)(ys zs : List A) → xs <>> ys ∈' zs → xs <>> ys ∈ zs
<>>'2<>> [] ys .ys refl = start ys
<>>'2<>> (xs :< x) ys zs p = bubble (<>>'2<>> xs (x ∷ ys) zs p)

_<><_∈'_ : ∀{A} → Bwd A → List A → Bwd A → Set
xs <>< ys ∈' zs = xs <>< ys ≡ zs

<><2<><' : ∀{A}(xs : Bwd A)(ys : List A)(zs : Bwd A)
  → xs <>< ys ∈ zs → xs <>< ys ∈' zs
<><2<><' xs [] .xs (start .xs) = refl
<><2<><' xs (y ∷ ys) zs (bubble p) = <><2<><' (xs :< y) ys zs p

<><'2<>< : ∀{A}(xs : Bwd A)(ys : List A)(zs : Bwd A)
  → xs <>< ys ∈' zs → xs <>< ys ∈ zs
<><'2<>< xs [] .xs refl = start xs
<><'2<>< xs (x ∷ ys) zs p = bubble (<><'2<>< (xs :< x) ys zs p)

lemma<><[] : ∀{A}(xs : Bwd A) → (xs <>< []) ≡ xs
lemma<><[] xs = refl

lemma[]<>> : ∀{A}(xs : List A) → ([] <>> xs) ≡ xs
lemma[]<>> xs = refl

-- convert a list to a backward list and back again

lemma<>1 : ∀{A}(xs : Bwd A)(ys : List A) → (xs <>< ys) <>> [] ≡ xs <>> ys
lemma<>1 xs []       = refl
lemma<>1 xs (x ∷ ys) = lemma<>1 (xs :< x) ys

lemma<>2 : ∀{A}(xs : Bwd A)(ys : List A) → ([] <>< (xs <>> ys)) ≡ xs <>< ys
lemma<>2 [] ys = refl
lemma<>2 (xs :< x) ys = lemma<>2 xs (x ∷ ys)

saturated : ∀{A}(as : List A) → ([] <>< as) <>> [] ∈ as
saturated as = <>>'2<>> ([] <>< as) [] as (lemma<>1 [] as)

lemma∷1 : ∀{A}(as as' : List A) → [] <>> as ∈ as' → as ≡ as'
lemma∷1 as .as (start .as) = refl

-- these properties are needed for bappTermLem
<>>-cancel-both : ∀{A}(az az' : Bwd A)(as : List A)
  → az <>> (az' <>> as) ∈ (az' <>> [])
  → az ≡ [] × as ≡ []
<>>-cancel-both az az' [] p =
  <>>-lcancel az (az' <>> []) (sym (<>>2<>>' az (az' <>> []) (az' <>> []) p))
  ,,
  refl
<>>-cancel-both az az' (a ∷ as) p = ⊥-elim (m+1+n≢0
  _
  (+-cancelʳ-≡
    _
    0
    (trans
      (trans
        (+-assoc (bwd-length az) (Data.List.length (a ∷ as)) (bwd-length az'))
        (trans
          (cong
            (bwd-length az Data.Nat.+_)
            (+-comm (Data.List.length (a ∷ as)) (bwd-length az')))
          (trans
            (cong
              (bwd-length az Data.Nat.+_)
              (sym (<>>-length az' (a ∷ as))))
            (trans
              (sym (<>>-length az (az' <>> (a ∷ as))))
              (trans
                (cong
                  Data.List.length
                  (<>>2<>>' az (az' <>> (a ∷ as)) (az' <>> []) p))
                (<>>-length az' []))))))
      (+-comm (bwd-length az') 0))))

<>>-cancel-both' : ∀{A}(az az' az'' : Bwd A)(as : List A)
  → az <>> (az' <>> as) ∈ (az'' <>> []) → bwd-length az' ≡ bwd-length az''
  → az ≡ [] × as ≡ [] × az' ≡ az''
<>>-cancel-both' az az' az'' [] p q
  with <>>-lcancel' az (az'' <>> []) (az' <>> []) (sym (<>>2<>>' _ _ _ p)) (trans (<>>-length az'' []) (trans (cong (Data.Nat._+ 0) (sym q)) (sym (<>>-length az' []))))
... | refl ,, Y = refl ,, refl ,, sym (trans (trans (sym (lemma<>2 az'' [])) (cong ([] <><_) Y)) (lemma<>2 az' []))
<>>-cancel-both' az az' az'' (a ∷ as) p q = ⊥-elim (m+1+n≢0
  _
  (+-cancelʳ-≡
    _
    0
    (trans
      (trans
        (+-assoc (bwd-length az) (Data.List.length (a ∷ as)) (bwd-length az'))
        (trans
          (cong
            (bwd-length az Data.Nat.+_)
            (+-comm (Data.List.length (a ∷ as)) (bwd-length az')))
          (trans
            (cong
              (bwd-length az Data.Nat.+_)
              (sym (<>>-length az' (a ∷ as))))
            (trans
              (sym (<>>-length az (az' <>> (a ∷ as))))
              (trans
                (cong
                  Data.List.length
                  (<>>2<>>' az (az' <>> (a ∷ as)) (az'' <>> []) p))
                (trans (<>>-length az'' []) (cong (Data.Nat._+ 0) (sym q))))))))
      (+-comm (bwd-length az') 0))))


open import Data.Product

_<L'_ : {A : Set} → List A → List A → Set
as <L' as' = Σ _ λ a → (a ∷ as) ≤L' as'

lem⊥ : ∀{A : Set}{as : List A}{a} → (a ∷ as) ≤L' [] → ⊥
lem⊥ (skip p) = lem⊥ p

lem0 : {A : Set}{a a' : A}{as as' : List A}
  → (a ∷ as) ≤L' (a' ∷ as') → as ≤L' as'
lem0 base     = base
lem0 (skip p) = skip (lem0 p)

lem1 : {A : Set}{a : A}{as as' : List A} → as ≤L' as' → as ≤L' (a ∷ as')
lem1 base = skip base
lem1 (skip p) = skip (lem1 p)

≤Lto≤L' : {A : Set}{as as' : List A} → as ≤L as' → as ≤L' as'
≤Lto≤L' base = base
≤Lto≤L' (skip p) = lem1 (≤Lto≤L' p)

[]≤L' : {A : Set}(as : List A) → [] ≤L' as
[]≤L' as = ≤Lto≤L' ([]≤L as)


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

Defined separetely here rather than using generic version used in the
typed syntax.

\begin{code}
open import Data.Integer
open import Data.String
open import Data.Bool

data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  unit       : TermCon
  Data       : DATA → TermCon

{-# FOREIGN GHC type TermCon = Some (ValueOf DefaultUni)               #-}
{-# FOREIGN GHC pattern TmInteger    i = Some (ValueOf DefaultUniInteger i) #-}
{-# FOREIGN GHC pattern TmByteString b = Some (ValueOf DefaultUniByteString b) #-}
{-# FOREIGN GHC pattern TmString     s = Some (ValueOf DefaultUniString s) #-}
{-# FOREIGN GHC pattern TmUnit         = Some (ValueOf DefaultUniUnit ()) #-}
{-# FOREIGN GHC pattern TmBool       b = Some (ValueOf DefaultUniBool b) #-}
{-# FOREIGN GHC pattern TmData       d = Some (ValueOf DefaultUniData d) #-}
{-# COMPILE GHC TermCon = data TermCon (TmInteger | TmByteString | TmString | TmBool | TmUnit | TmData) #-}
\end{code}
