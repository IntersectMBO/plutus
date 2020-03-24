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
open import Data.Bool using (Bool)
open import Data.Char using (Char)

open import Data.Vec hiding (_>>=_; map; _++_; [_])
open import Utils
open import Relation.Nullary
open import Category.Monad
import Level
open RawMonad {f = Level.zero} (record { return = just ; _>>=_ = λ { (just x) f → f x ; nothing x → nothing} })


open import Builtin.Constant.Type
open import Builtin
open import Raw

\end{code}

\begin{code}

open import Type

data ScopedTy (n : ℕ) : Set where
  `    : Fin n → ScopedTy n
  _⇒_  : ScopedTy n → ScopedTy n → ScopedTy n
  Π    : Kind → ScopedTy (suc n) → ScopedTy n
  ƛ    : Kind → ScopedTy (suc n) → ScopedTy n
  _·_  : ScopedTy n → ScopedTy n → ScopedTy n
  con  : TyCon → ScopedTy n
  μ    : ScopedTy n → ScopedTy n → ScopedTy n

--{-# COMPILE GHC ScopedTy = data ScTy (ScTyVar | ScTyFun | ScTyPi | ScTyLambda | ScTyApp | ScTyCon) #-}

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
lookupWTm (suc x) (S w) = map suc (lookupWTm x w)
lookupWTm (suc x) (T w) = lookupWTm x w

lookupWTy : ∀(x : ℕ){n}(w : Weirdℕ n) → Maybe ℕ
lookupWTy zero Z = nothing
lookupWTy zero (S w) = nothing
lookupWTy zero (T w) = just 0
lookupWTy (suc x) Z = nothing
lookupWTy (suc x) (S w) = lookupWTy x w
lookupWTy (suc x) (T w) = map suc (lookupWTy x w)

lookupWTm' : ∀(x : ℕ){n} → Weirdℕ n → ℕ
lookupWTm' x (S m) = lookupWTm' x m
lookupWTm' x (T m) = lookupWTm' (suc x) m
lookupWTm' x Z     = x

lookupWTy' : ∀(x : ℕ){n} → Weirdℕ n → ℕ
lookupWTy' x (S m) = lookupWTy' (suc x) m
lookupWTy' x (T m) = lookupWTy' x m
lookupWTy' x Z     = x

-- these are renamings
shifterTy : ∀(m : ℕ){n}(w : Weirdℕ n) → RawTy → RawTy
shifterTy m w (` x) = ` (maybe (\x → x) 100 (lookupWTy ∣ x - 1 ∣  w))
shifterTy m w (A ⇒ B) = shifterTy m w A ⇒ shifterTy m w B
shifterTy m w (Π K A) = Π K (shifterTy (suc m) (T w) A)
shifterTy m w (ƛ K A) = ƛ K (shifterTy (suc m) (T w) A)
shifterTy m w (A · B) = shifterTy m w A · shifterTy m w B
shifterTy m w (con c) = con c
shifterTy m w (μ A B) = μ (shifterTy m w A) (shifterTy m w B)

shifter : ∀(m : ℕ){n}(w : Weirdℕ n) → RawTm → RawTm
shifter m w (` x) = ` (maybe (\x → x) 100 (lookupWTm ∣ x - 1 ∣ w))
shifter m w (Λ K t) = Λ K (shifter (suc m) (T w) t)
shifter m w (t ·⋆ A) = shifter m w t ·⋆ shifterTy m w A
shifter m w (ƛ A t) = ƛ (shifterTy (suc m) (S w) A) (shifter (suc m) (S w) t) 
shifter m w (t · u) = shifter m w t · shifter m w u
shifter m w (con c) = con c
shifter m w (error A) = error (shifterTy m w A)
shifter m w (builtin b) = builtin b
shifter m w (wrap pat arg t) =
  wrap (shifterTy m w pat) (shifterTy m w arg) (shifter m w t)
shifter m w (unwrap t) = unwrap (shifter m w t)

unshifterTy : ∀{n} → Weirdℕ n → RawTy → RawTy
unshifterTy w (` x) = ` (suc (lookupWTy' x w))
unshifterTy w (A ⇒ B) = unshifterTy w A ⇒ unshifterTy w B
unshifterTy w (Π K A) = Π K (unshifterTy (T w) A)
unshifterTy w (ƛ K A) = ƛ K (unshifterTy (T w) A)
unshifterTy w (A · B) = unshifterTy w A · unshifterTy w B
unshifterTy w (con c) = con c
unshifterTy w (μ A B) = μ (unshifterTy w A) (unshifterTy w B)


unshifter : ∀{n} → Weirdℕ n → RawTm → RawTm
unshifter w (` x) = ` (suc (lookupWTm' x w))
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

data ScopedTm {n}(w : Weirdℕ n) : Set where
  `    :    WeirdFin w → ScopedTm w
  Λ    :    Kind → ScopedTm (T w) → ScopedTm w
  _·⋆_ :    ScopedTm w → ScopedTy n → ScopedTm w
  ƛ    :    ScopedTy n → ScopedTm (S w) → ScopedTm w
  _·_  :    ScopedTm w → ScopedTm w → ScopedTm w
  con  :    TermCon → ScopedTm w
  error :   ScopedTy n → ScopedTm w
  builtin : (bn : Builtin) → List (ScopedTy n) → List (ScopedTm w)
            → ScopedTm w
  wrap :    ScopedTy n → ScopedTy n → ScopedTm w → ScopedTm w
  unwrap :  ScopedTm w → ScopedTm w

-- SCOPE CHECKING / CONVERSION FROM RAW TO SCOPED

-- should just use ordinary kind for everything

deBruijnifyK : RawKind → Kind
deBruijnifyK * = *
deBruijnifyK (K ⇒ J) = deBruijnifyK K ⇒ deBruijnifyK J

deBruijnifyC : RawTermCon → TermCon
deBruijnifyC (integer i)    = integer i
deBruijnifyC (bytestring b) = bytestring b
deBruijnifyC (string s)     = string s
deBruijnifyC (bool b)       = bool b
deBruijnifyC (char c)       = char c
deBruijnifyC unit           = unit 

ℕtoFin : ∀{n} → ℕ → Maybe (Fin n)
ℕtoFin {zero}  _       = nothing
ℕtoFin {suc m} zero    = just zero
ℕtoFin {suc m} (suc n) = map suc (ℕtoFin n)

ℕtoWeirdFin : ∀{n}{w : Weirdℕ n} → ℕ → Maybe (WeirdFin w)
ℕtoWeirdFin {w = Z}   n    = nothing
ℕtoWeirdFin {w = S w} zero = just Z
ℕtoWeirdFin {w = S w} (suc n) with ℕtoWeirdFin {w = w} n
ℕtoWeirdFin {_} {S w} (suc n) | just i  = just (S i)
ℕtoWeirdFin {_} {S w} (suc n) | nothing = nothing
ℕtoWeirdFin {w = T w} n  with ℕtoWeirdFin {w = w} n
ℕtoWeirdFin {_} {T w} n | just x  = just (T x)
ℕtoWeirdFin {_} {T w} n | nothing = nothing

scopeCheckTy : ∀{n} → RawTy → Maybe (ScopedTy n)
scopeCheckTy (` x) = map ` (ℕtoFin x)
scopeCheckTy (A ⇒ B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A ⇒ B)
scopeCheckTy (Π K A) = map (Π (deBruijnifyK K)) (scopeCheckTy A)
scopeCheckTy (ƛ K A) = map (ƛ (deBruijnifyK K)) (scopeCheckTy A)
scopeCheckTy (A · B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A · B)
scopeCheckTy (con c) = just (con c)
scopeCheckTy (μ A B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (μ A B)

scopeCheckTm : ∀{n}{w : Weirdℕ n} → RawTm → Maybe (ScopedTm w)
scopeCheckTm (` x) = map ` (ℕtoWeirdFin x)
scopeCheckTm {n}{w}(Λ K t) = map (Λ (deBruijnifyK K)) (scopeCheckTm {suc n}{T w} t)
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
scopeCheckTm (con c) = just (con (deBruijnifyC c))
scopeCheckTm (error A) = map error (scopeCheckTy A)
scopeCheckTm (builtin b) = just (builtin b [] [])
scopeCheckTm (wrap A B t) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  t ← scopeCheckTm t
  return (wrap A B t)
scopeCheckTm (unwrap t) = map unwrap (scopeCheckTm t)
\end{code}

-- SATURATION OF BUILTINS

\begin{code}
open import Data.Product
open import Data.Sum

builtinMatcher : ∀{n}{w : Weirdℕ n} → ScopedTm w
  → (Builtin × List (ScopedTy n) × List (ScopedTm w)) ⊎ ScopedTm w
builtinMatcher (builtin b As ts) = inj₁ (b , As , ts)
builtinMatcher t              = inj₂ t

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

arity⋆ : Builtin → ℕ
arity⋆ ifThenElse = 1
arity⋆ _ = 0

open import Relation.Nullary

builtinEater : ∀{n}{w : Weirdℕ n} → Builtin
 → List (ScopedTy n) → List (ScopedTm w) → ScopedTm w → ScopedTm w
builtinEater b As ts u
  with Data.List.length ts Data.Nat.+ 1 Data.Nat.≤? arity b
builtinEater b As ts u | yes p = builtin b As (ts Data.List.++ [ u ])
builtinEater b As ts u | no ¬p = builtin b As ts · u

builtinEater⋆ : ∀{n}{w : Weirdℕ n} → Builtin
  → List (ScopedTy n) → List (ScopedTm w) → ScopedTy n → ScopedTm w
builtinEater⋆ b As ts A
  with Data.List.length ts Data.Nat.+ 1 Data.Nat.≤? arity⋆ b
builtinEater⋆ b As ts A | yes p = builtin b (As Data.List.++ [ A ]) ts
builtinEater⋆ b As ts A | no ¬p = builtin b As ts ·⋆ A

saturate : ∀{n}{w : Weirdℕ n} → ScopedTm w → ScopedTm w
saturate (` x)          = ` x
saturate (Λ K t)        = Λ K (saturate t)
saturate (t ·⋆ A)       with builtinMatcher (saturate t)
saturate (t ·⋆ A) | inj₁ (b , As , ts) = builtinEater⋆ b As ts A
saturate (t ·⋆ A) | inj₂ t'            = t' ·⋆ A
saturate (ƛ A t)        = ƛ A (saturate t)
saturate (t · u)        with builtinMatcher (saturate t)
saturate (t · u) | inj₁ (b , As , ts) = builtinEater b As ts (saturate u)
saturate (t · u) | inj₂ t'            = t' · saturate u
saturate (con c)        = con c
saturate (error A)      = error A
saturate (builtin b As ts) = builtin b As ts
saturate (wrap A B t) = wrap A B (saturate t)
saturate (unwrap t)   = unwrap (saturate t)

-- I don't think As or ts can be unsaturated, could be enforced by
  -- seperate representations for sat and unsat terms
\end{code}

\begin{code}
{-# TERMINATING #-}
unsaturate : ∀{n}{w : Weirdℕ n} → ScopedTm w → ScopedTm w

builtinBuilder : ∀{n}{w : Weirdℕ n} → Builtin → List (ScopedTy n) → List (ScopedTm w) → ScopedTm w
builtinBuilder b [] [] = builtin b [] []
builtinBuilder b (A ∷ As) [] = builtinBuilder b As [] ·⋆ A
builtinBuilder b As (t ∷ ts) = builtinBuilder b As ts · unsaturate t
\end{code}

\begin{code}
unsaturate (` x) = ` x
unsaturate (Λ K t) = Λ K (unsaturate t)
unsaturate (t ·⋆ A) = unsaturate t ·⋆ A
unsaturate (ƛ A t) = ƛ A (unsaturate t)
unsaturate (t · u) = unsaturate t · unsaturate u
unsaturate (con c) = con c
unsaturate (error A) = error A
unsaturate (builtin b As bs) =
  builtinBuilder b (Data.List.reverse As) (Data.List.reverse bs)
unsaturate (wrap A B t) = wrap A B (unsaturate t)
unsaturate (unwrap t)   = unwrap (unsaturate t)
\end{code}

\begin{code}
unDeBruijnifyK : Kind → RawKind
unDeBruijnifyK * = *
unDeBruijnifyK (K ⇒ J) = unDeBruijnifyK K ⇒ unDeBruijnifyK J
\end{code}

\begin{code}
wftoℕ : ∀{n}{w : Weirdℕ n} → WeirdFin w → ℕ
wftoℕ Z = zero
wftoℕ (S i) = ℕ.suc (wftoℕ i)
wftoℕ (T i) = ℕ.suc (wftoℕ i)
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

extricateScope : ∀{n}{w : Weirdℕ n} → ScopedTm w → RawTm
extricateScope (` x) = ` (WeirdFintoℕ x)
extricateScope (Λ K t) = Λ (unDeBruijnifyK K) (extricateScope t)
extricateScope (t ·⋆ A) = extricateScope t ·⋆ extricateScopeTy A
extricateScope (ƛ A t) = ƛ (extricateScopeTy A) (extricateScope t)
extricateScope (t · u) = extricateScope t · extricateScope u
extricateScope (con c) = con (unDeBruijnifyC c)
extricateScope (error A) = error (extricateScopeTy A)
extricateScope (builtin bn _ _) = builtin bn
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

{-
uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " ++ Data.Integer.show x ++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon size = "size"
-}

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
ugly (builtin b As ts) =
  "(builtin " ++
  uglyBuiltin b ++
  " " ++
  Data.Integer.show (Data.Integer.ℤ.pos (Data.List.length As)) ++
  " " ++
  Data.Integer.show (Data.Integer.ℤ.pos (Data.List.length ts))
  ++ ")"
ugly (error _) = "error _"
ugly (wrap _ _ t) = "(wrap " ++ ugly t ++ ")"
ugly (unwrap t) = "(unwrap " ++ ugly t ++ ")"
\end{code}
