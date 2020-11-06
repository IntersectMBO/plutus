\begin{code}
module Scoped where
\end{code}

\begin{code}
open import Data.Nat hiding (_*_)
open import Data.Fin hiding (_-_;_+_;_<_)
open import Data.List hiding (map; _++_)
open import Data.Integer hiding (_*_; suc;_-_;_+_;_<_)
open import Data.String hiding (_<_)
open import Data.Unit
open import Data.Vec using (Vec;[];_∷_)
open import Data.Bool using (Bool)
open import Data.Char using (Char)
open import Data.Product using (_×_;_,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl)
open import Data.Sum using (_⊎_;inj₁)
open import Relation.Nullary
open import Category.Monad
import Level

open import Builtin.Constant.Type
open import Builtin
open import Raw
open import Utils
\end{code}

\begin{code}
arity : Builtin → ℕ
arity addInteger = 2
arity subtractInteger = 2
arity multiplyInteger = 2
arity divideInteger = 2
arity quotientInteger = 2
arity remainderInteger = 2
arity modInteger = 2
arity lessThanInteger = 2
arity lessThanEqualsInteger = 2
arity greaterThanInteger = 2
arity greaterThanEqualsInteger = 2
arity equalsInteger = 2
arity concatenate = 2
arity takeByteString = 2
arity dropByteString = 2
arity sha2-256 = 1
arity sha3-256 = 1
arity verifySignature = 3
arity equalsByteString = 2
arity ifThenElse = 3
arity charToString = 1
arity append = 2
arity trace = 1

arity⋆ : Builtin → ℕ
arity⋆ ifThenElse = 1
arity⋆ _ = 0

open import Type

data ScopedTy (n : ℕ) : Set where
  `    : Fin n → ScopedTy n
  _⇒_  : ScopedTy n → ScopedTy n → ScopedTy n
  Π    : Kind → ScopedTy (suc n) → ScopedTy n
  ƛ    : Kind → ScopedTy (suc n) → ScopedTy n
  _·_  : ScopedTy n → ScopedTy n → ScopedTy n
  con  : TyCon → ScopedTy n
  μ    : ScopedTy n → ScopedTy n → ScopedTy n
  missing : ScopedTy n -- for when things compute to error

Tel⋆ : ℕ → ℕ → Set
Tel⋆ n m = Vec (ScopedTy n) m

open import Builtin.Signature ℕ ⊤ 0 (λ n _ → suc n) tt (λ n _ → Fin n) zero suc (λ n _ → ScopedTy n) ` con

-- variables

data Weirdℕ : ℕ → Set where
  Z : Weirdℕ 0
  S : ∀{n} → Weirdℕ n  → Weirdℕ n
  T : ∀{n} → Weirdℕ n → Weirdℕ (suc n)

data WeirdFin : ∀{n} → Weirdℕ n → Set where
  Z : ∀{n}{w : Weirdℕ n} → WeirdFin (S w)
  S : ∀{n}{w : Weirdℕ n} → WeirdFin w → WeirdFin (S w)
  T : ∀{n}{w : Weirdℕ n} → WeirdFin w → WeirdFin (T w)


-- what is this for?
-- there are two meaningful things here:
-- 1. one to literally convert the number
-- 2. to extract a type context from a term one
-- this looks like (1)

wtoℕ : ∀{n} → Weirdℕ n → ℕ
wtoℕ Z = zero
wtoℕ (S x) = suc (wtoℕ x)
wtoℕ (T x) = suc (wtoℕ x)

WeirdFintoℕ : ∀{n}{w : Weirdℕ n} → WeirdFin w → ℕ
WeirdFintoℕ Z     = 0
WeirdFintoℕ (S i) = suc (WeirdFintoℕ i)
WeirdFintoℕ (T i) = WeirdFintoℕ i

-- extract number of term binders we are under
wtoℕTm : ∀{n} → Weirdℕ n → ℕ
wtoℕTm Z = zero
wtoℕTm (S x) = suc (wtoℕTm x)
wtoℕTm (T x) = wtoℕTm x

wtoℕTy : ∀{n} → Weirdℕ n → ℕ
wtoℕTy Z     = zero
wtoℕTy (S x) = wtoℕTm x
wtoℕTy (T x) = suc (wtoℕTm x)


-- extract the number of type binders

lookupWTm : ∀(x : ℕ){n}(w : Weirdℕ n) → Maybe ℕ
lookupWTm zero Z = nothing
lookupWTm zero (S w) = just 0
lookupWTm zero (T w) = nothing
lookupWTm (suc x) Z = nothing
lookupWTm (suc x) (S w) = fmap suc (lookupWTm x w)
lookupWTm (suc x) (T w) = lookupWTm x w

lookupWTy : ∀(x : ℕ){n}(w : Weirdℕ n) → Maybe ℕ
lookupWTy zero Z = nothing
lookupWTy zero (S w) = nothing
lookupWTy zero (T w) = just 0
lookupWTy (suc x) Z = nothing
lookupWTy (suc x) (S w) = lookupWTy x w
lookupWTy (suc x) (T w) = fmap suc (lookupWTy x w)


lookupWTm' : ∀(x : ℕ){n} → Weirdℕ n → ℕ
lookupWTm' i Z = i
lookupWTm' zero (S w) = 1
lookupWTm' (suc i) (S w) = suc (lookupWTm' i w)
lookupWTm' i (T w) = suc (lookupWTm' i w)
{-
lookupWTm' x (S m) = lookupWTm' x m
lookupWTm' x (T m) = lookupWTm' (suc x) m
lookupWTm' x Z     = suc x
-}

lookupWTy' : ∀(x : ℕ){n} → Weirdℕ n → ℕ
lookupWTy' i Z = i
lookupWTy' i (S w) = suc (lookupWTy' i w)
lookupWTy' (suc i) (T w) = suc (lookupWTy' i w)
lookupWTy' 0 (T w) = 1

{-
lookupWTy' x (S m) = lookupWTy' (suc x) m
lookupWTy' x (T m) = lookupWTy' x m
lookupWTy' x Z     = suc x
-}

-- these are renamings
shifterTy : ∀{n}(w : Weirdℕ n) → RawTy → RawTy
shifterTy w (` x) = ` (maybe (\x → x) 100 (lookupWTy ∣ x - 1 ∣  w))
shifterTy w (A ⇒ B) = shifterTy w A ⇒ shifterTy w B
shifterTy w (Π K A) = Π K (shifterTy (T w) A)
shifterTy w (ƛ K A) = ƛ K (shifterTy (T w) A)
shifterTy w (A · B) = shifterTy w A · shifterTy w B
shifterTy w (con c) = con c
shifterTy w (μ A B) = μ (shifterTy w A) (shifterTy w B)

shifter : ∀{n}(w : Weirdℕ n) → RawTm → RawTm
shifter w (` x) = ` (maybe (\x → x) 100 (lookupWTm ∣ x - 1 ∣ w))
shifter w (Λ K t) = Λ K (shifter (T w) t)
shifter w (t ·⋆ A) = shifter w t ·⋆ shifterTy w A
shifter w (ƛ A t) = ƛ (shifterTy (S w) A) (shifter (S w) t)
shifter w (t · u) = shifter w t · shifter w u
shifter w (con c) = con c
shifter w (error A) = error (shifterTy w A)
shifter w (builtin b) = builtin b
shifter w (wrap pat arg t) =
  wrap (shifterTy w pat) (shifterTy w arg) (shifter w t)
shifter w (unwrap t) = unwrap (shifter w t)

unshifterTy : ∀{n} → Weirdℕ n → RawTy → RawTy
unshifterTy w (` x) = ` (lookupWTy' x w)
unshifterTy w (A ⇒ B) = unshifterTy w A ⇒ unshifterTy w B
unshifterTy w (Π K A) = Π K (unshifterTy (T w) A)
unshifterTy w (ƛ K A) = ƛ K (unshifterTy (T w) A)
unshifterTy w (A · B) = unshifterTy w A · unshifterTy w B
unshifterTy w (con c) = con c
unshifterTy w (μ A B) = μ (unshifterTy w A) (unshifterTy w B)

open import Relation.Binary.PropositionalEquality

unshifter : ∀{n} → Weirdℕ n → RawTm → RawTm
unshifter w (` x) = ` (lookupWTm' x w)
unshifter w (Λ K t) = Λ K (unshifter (T w) t)

unshifter w (t ·⋆ A) = unshifter w t ·⋆ unshifterTy w A
unshifter w (ƛ A t) = ƛ (unshifterTy (S w) A) (unshifter (S w) t)
unshifter w (t · u) = unshifter w t · unshifter w u
unshifter w (con c) = con c
unshifter w (error A) = error (unshifterTy w A)
unshifter w (builtin b) = builtin b
unshifter w (wrap pat arg t) =
  wrap (unshifterTy w pat) (unshifterTy w arg) (unshifter w t)
unshifter w (unwrap t) = unwrap (unshifter w t)

data TermCon : Set where
  integer    : (i : ℤ) → TermCon
  bytestring : (b : ByteString) → TermCon
  string     : (s : String) → TermCon
  bool       : (b : Bool) → TermCon
  char       : (c : Char) → TermCon
  unit       : TermCon

Tel : ∀{n} → Weirdℕ n → ℕ → Set

data ScopedTm {n}(w : Weirdℕ n) : Set where
  `    :    WeirdFin w → ScopedTm w
  Λ    :    Kind → ScopedTm (T w) → ScopedTm w
  _·⋆_ :    ScopedTm w → ScopedTy n → ScopedTm w
  ƛ    :    ScopedTy n → ScopedTm (S w) → ScopedTm w
  _·_  :    ScopedTm w → ScopedTm w → ScopedTm w
  con  :    TermCon → ScopedTm w
  error :   ScopedTy n → ScopedTm w
  builtin : (b : Builtin) 
    → ∀{m o}
    → (m ≤‴ arity⋆ b × o ≡ 0) ⊎ (m ≡ arity⋆ b × o ≤‴ arity b)
    → Tel⋆ n m
    → Tel w o
    → ScopedTm w
  wrap :    ScopedTy n → ScopedTy n → ScopedTm w → ScopedTm w
  unwrap :  ScopedTm w → ScopedTm w

Tel w n = Vec (ScopedTm w) n

-- SCOPE CHECKING / CONVERSION FROM RAW TO SCOPED

-- should just use ordinary kind for everything

deBruijnifyK : RawKind → Kind
deBruijnifyK * = *
deBruijnifyK (K ⇒ J) = deBruijnifyK K ⇒ deBruijnifyK J

{-# COMPILE GHC deBruijnifyK as deBruijnifyK #-}

deBruijnifyC : RawTermCon → TermCon
deBruijnifyC (integer i)    = integer i
deBruijnifyC (bytestring b) = bytestring b
deBruijnifyC (string s)     = string s
deBruijnifyC (bool b)       = bool b
deBruijnifyC (char c)       = char c
deBruijnifyC unit           = unit

postulate
  FreeVariableError : Set

{-# COMPILE GHC FreeVariableError = type FreeVariableError #-}


data ScopeError : Set where
  deBError : ScopeError
  freeVariableError : FreeVariableError → ScopeError

{-# FOREIGN GHC import Language.PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC ScopeError = data ScopeError (DeBError | FreeVariableError) #-}


ℕtoFin : ∀{n} → ℕ → Either ScopeError (Fin n)
ℕtoFin {zero}  _       = inj₁ deBError
ℕtoFin {suc m} zero    = return zero
ℕtoFin {suc m} (suc n) = fmap suc (ℕtoFin n)

ℕtoWeirdFin : ∀{n}{w : Weirdℕ n} → ℕ → Either ScopeError (WeirdFin w)
ℕtoWeirdFin {w = Z}   n    = inj₁ deBError
ℕtoWeirdFin {w = S w} zero = return Z
ℕtoWeirdFin {w = S w} (suc n) = do
  i ← ℕtoWeirdFin {w = w} n
  return (S i)
ℕtoWeirdFin {w = T w} n  = do
  i ← ℕtoWeirdFin {w = w} n
  return (T i)

scopeCheckTy : ∀{n} → RawTy → Either ScopeError (ScopedTy n)
scopeCheckTy (` x) = fmap ` (ℕtoFin x)
scopeCheckTy (A ⇒ B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A ⇒ B)
scopeCheckTy (Π K A) = fmap (Π (deBruijnifyK K)) (scopeCheckTy A)
scopeCheckTy (ƛ K A) = fmap (ƛ (deBruijnifyK K)) (scopeCheckTy A)
scopeCheckTy (A · B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A · B)
scopeCheckTy (con c) = inj₂ (con c)
scopeCheckTy (μ A B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (μ A B)

scopeCheckTm : ∀{n}{w : Weirdℕ n} → RawTm → Either ScopeError (ScopedTm w)
scopeCheckTm (` x) = fmap ` (ℕtoWeirdFin x)
scopeCheckTm {n}{w}(Λ K t) = fmap (Λ (deBruijnifyK K)) (scopeCheckTm {suc n}{T w} t)
scopeCheckTm (t ·⋆ A) = do
  A ← scopeCheckTy A
  t ← scopeCheckTm t
  return (t ·⋆ A)
scopeCheckTm (ƛ A t) = do
  A ← scopeCheckTy A
  t ← scopeCheckTm t
  return (ƛ A t)
scopeCheckTm (t · u) = do
  t ← scopeCheckTm t
  u ← scopeCheckTm u
  return (t · u)
scopeCheckTm (con c) = return (con (deBruijnifyC c))
scopeCheckTm (error A) = fmap error (scopeCheckTy A)
scopeCheckTm (builtin b) = return (builtin b (inj₁ (z≤‴n , refl)) [] [])
scopeCheckTm (wrap A B t) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  t ← scopeCheckTm t
  return (wrap A B t)
scopeCheckTm (unwrap t) = fmap unwrap (scopeCheckTm t)
\end{code}

\begin{code}
unDeBruijnifyK : Kind → RawKind
unDeBruijnifyK * = *
unDeBruijnifyK (K ⇒ J) = unDeBruijnifyK K ⇒ unDeBruijnifyK J

{-# COMPILE GHC unDeBruijnifyK as unDeBruijnifyK #-}

\end{code}

\begin{code}
{-
wftoℕ : ∀{n}{w : Weirdℕ n} → WeirdFin w → ℕ
wftoℕ Z = zero
wftoℕ (S i) = ℕ.suc (wftoℕ i)
wftoℕ (T i) = ℕ.suc (wftoℕ i)
-}
\end{code}

\begin{code}
unDeBruijnifyC : TermCon → RawTermCon
unDeBruijnifyC (integer i)    = integer i
unDeBruijnifyC (bytestring b) = bytestring b
unDeBruijnifyC (string s)     = string s
unDeBruijnifyC (bool b)       = bool b
unDeBruijnifyC (char c)       = char c
unDeBruijnifyC unit           = unit
\end{code}

\begin{code}
extricateScopeTy : ∀{n} → ScopedTy n → RawTy
extricateScopeTy (` x) = ` (toℕ x)
extricateScopeTy (A ⇒ B) = extricateScopeTy A ⇒ extricateScopeTy B
extricateScopeTy (Π K A) = Π (unDeBruijnifyK K) (extricateScopeTy A)
extricateScopeTy (ƛ K A) = ƛ (unDeBruijnifyK K) (extricateScopeTy A)
extricateScopeTy (A · B) = extricateScopeTy A · extricateScopeTy B
extricateScopeTy (con c) = con c
extricateScopeTy (μ A B) = μ (extricateScopeTy A) (extricateScopeTy B)
extricateScopeTy missing = con bool -- TODO

extricateScope : ∀{n}{w : Weirdℕ n} → ScopedTm w → RawTm
extricateScope (` x) = ` (WeirdFintoℕ x)
extricateScope (Λ K t) = Λ (unDeBruijnifyK K) (extricateScope t)
extricateScope (t ·⋆ A) = extricateScope t ·⋆ extricateScopeTy A
extricateScope (ƛ A t) = ƛ (extricateScopeTy A) (extricateScope t)
extricateScope (t · u) = extricateScope t · extricateScope u
extricateScope (con c) = con (unDeBruijnifyC c)
extricateScope (error A) = error (extricateScopeTy A)
extricateScope (builtin bn _ _ _) = builtin bn -- TODO
extricateScope (wrap pat arg t) =
  wrap (extricateScopeTy pat) (extricateScopeTy arg) (extricateScope t)
extricateScope (unwrap t) = unwrap (extricateScope t)
\end{code}

-- UGLY PRINTING

\begin{code}
open import Data.String

uglyWeirdFin : ∀{n}{w : Weirdℕ n} → WeirdFin w → String
uglyWeirdFin Z = "0"
uglyWeirdFin (T x) = "(T " ++ uglyWeirdFin x ++ ")"
uglyWeirdFin (S x) = "(S " ++ uglyWeirdFin x ++ ")"

uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " ++ Data.Integer.show x ++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon size = "size"

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"
ugly : ∀{n}{w : Weirdℕ n} → ScopedTm w → String
ugly (` x) = "(` " ++ uglyWeirdFin x ++ ")"
ugly (ƛ _ t) = "(ƛ " ++ ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (Λ _ t) = "(Λ " ++ ugly t ++ ")"
ugly (t ·⋆ A) = "( " ++ ugly t ++ " ·⋆ " ++ "TYPE" ++ ")"

ugly (con c) = "(con " -- ++ uglyTermCon c ++ ")"
ugly (builtin b X As ts) = "builtin" -- FIX ME
{-  "(builtin " ++
  uglyBuiltin b ++
  " " ++
  Data.Integer.show (Data.Integer.ℤ.pos (Data.List.length As)) ++
  " " ++
  Data.Integer.show (Data.Integer.ℤ.pos (Data.List.length ts))
  ++ ")" -}
ugly (error _) = "error _"
ugly (wrap _ _ t) = "(wrap " ++ ugly t ++ ")"
ugly (unwrap t) = "(unwrap " ++ ugly t ++ ")"
\end{code}
