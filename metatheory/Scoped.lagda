\begin{code}
module Scoped where
\end{code}

\begin{code}
open import Data.Nat hiding (_*_)
open import Data.Fin hiding (_-_)
open import Data.List hiding (map; _++_)
open import Data.Integer hiding (_*_; suc)
open import Data.String
open import Data.Unit

open import Builtin.Constant.Type
open import Builtin
open import Raw

\end{code}

\begin{code}
data ScopedKind : Set where
  *   : ScopedKind
  _⇒_ : ScopedKind → ScopedKind → ScopedKind

{-# FOREIGN GHC import Scoped #-}
{-# COMPILE GHC ScopedKind = data ScKind (ScKiStar | ScKiFun) #-}

data ScopedTy (n : ℕ) : Set where
  `    : Fin n → ScopedTy n
  _⇒_  : ScopedTy n → ScopedTy n → ScopedTy n
  Π    : String → ScopedKind → ScopedTy (suc n) → ScopedTy n
  ƛ    : String → ScopedKind → ScopedTy (suc n) → ScopedTy n
  _·_  : ScopedTy n → ScopedTy n → ScopedTy n
  con  : TyCon → ScopedTy n
  μ    : ScopedTy n → ScopedTy n → ScopedTy n

--{-# COMPILE GHC ScopedTy = data ScTy (ScTyVar | ScTyFun | ScTyPi | ScTyLambda | ScTyApp | ScTyCon) #-}

-- type synonyms

boolean : ∀{Γ} → ScopedTy Γ
boolean = Π "α" * (` zero ⇒ (` zero ⇒ ` zero))

unit : ∀{Γ} → ScopedTy Γ
unit = Π "α" * (` zero ⇒ (` zero ⇒ ` zero))

open import Builtin.Signature ℕ ⊤ 0 (λ n _ → suc n) tt (λ n _ → Fin n) zero suc (λ n _ → ScopedTy n) ` con boolean

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

data TermCon : Set where
  integer    : (i : ℤ) → TermCon
  bytestring : (b : ByteString) → TermCon
  string     : String → TermCon

data ScopedTm {n}(w : Weirdℕ n) : Set where
  `    :    WeirdFin w → ScopedTm w
  Λ    :    String → ScopedKind → ScopedTm (T w) → ScopedTm w
  _·⋆_ :    ScopedTm w → ScopedTy n → ScopedTm w
  ƛ    :    String → ScopedTy n → ScopedTm (S w) → ScopedTm w
  _·_  :    ScopedTm w → ScopedTm w → ScopedTm w
  con  :    TermCon → ScopedTm w
  error :   ScopedTy n → ScopedTm w
  builtin : (bn : Builtin) → List (ScopedTy n) → List (ScopedTm w)
            → ScopedTm w
  wrap :    ScopedTy n → ScopedTy n → ScopedTm w → ScopedTm w
  unwrap :  ScopedTm w → ScopedTm w

-- term synonyms
void : ∀{Φ}{Γ : Weirdℕ Φ} → ScopedTm Γ
void = Λ "α" * (ƛ "x" (` zero) (` Z))

true : ∀{Φ}{Γ : Weirdℕ Φ} → ScopedTm Γ
true = Λ "α" * (ƛ "t" (` zero) (ƛ "f" (` zero) (` (S Z))))

false : ∀{Φ}{Γ : Weirdℕ Φ} → ScopedTm Γ
false = Λ "α" * (ƛ "t" (` zero) (ƛ "f" (` zero) (` Z)))


-- SCOPE CHECKING / CONVERSION FROM RAW TO SCOPED

-- should just use ordinary kind for everything

deBruijnifyK : RawKind → ScopedKind
deBruijnifyK * = *
deBruijnifyK (K ⇒ J) = deBruijnifyK K ⇒ deBruijnifyK J

open import Data.Vec hiding (_>>=_; map; _++_; [_])
open import Utils
open import Data.String
open import Relation.Nullary
open import Category.Monad
import Level
open RawMonad {f = Level.zero} (record { return = just ; _>>=_ = λ { (just x) f → f x ; nothing x → nothing} })

velemIndex : String → ∀{n} → Vec String n → Maybe (Fin n)
velemIndex x [] = nothing
velemIndex x (x' ∷ xs) with x Data.String.≟ x'
velemIndex x (x' ∷ xs) | yes p = just zero
velemIndex x (x' ∷ xs) | no ¬p = map Fin.suc (velemIndex x xs)

deBruijnifyTy : ∀{n} → Vec String n → RawTy → Maybe (ScopedTy n)
deBruijnifyTy g (` α) = map ` (velemIndex α g)
deBruijnifyTy g (A ⇒ B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A ⇒ B)
deBruijnifyTy g (Π x K B) =
  map (Π x (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (ƛ x K B) =
  map (ƛ x (deBruijnifyK K)) (deBruijnifyTy (x ∷ g) B)
deBruijnifyTy g (A · B) = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (A · B)
deBruijnifyTy g (con b)     = just (con b)
deBruijnifyTy g (μ A B)     = do
  A ← deBruijnifyTy g A
  B ← deBruijnifyTy g B
  return (μ A B)


data WeirdVec (X : Set) : ∀{n} → Weirdℕ n → Set where
  nil : WeirdVec X Z
  consS : ∀{n}{w : Weirdℕ n} → X → WeirdVec X w → WeirdVec X (S w)
  consT : ∀{n}{w : Weirdℕ n} → X → WeirdVec X w → WeirdVec X (T w)

∥_∥Vec : ∀{X}{n}{w : Weirdℕ n} → WeirdVec X w → Vec X n
∥ nil        ∥Vec = []
∥ consS x xs ∥Vec = ∥ xs ∥Vec
∥ consT x xs ∥Vec = x ∷ ∥ xs ∥Vec

velemIndexWeird : String → ∀{n}{w : Weirdℕ n} → WeirdVec String w → Maybe (WeirdFin w)
velemIndexWeird x nil = nothing
velemIndexWeird x (consS x' xs) with x Data.String.≟ x'
velemIndexWeird x (consS x' xs) | yes p = just Z
velemIndexWeird x (consS _  xs) | no ¬p = map S (velemIndexWeird x xs)
velemIndexWeird x (consT _  xs) = map T (velemIndexWeird x xs)

lookupWeird  : ∀{X}{n}{w : Weirdℕ n} → WeirdVec X w → WeirdFin w → X
lookupWeird (consS x xs) Z = x
lookupWeird (consS x xs) (S i) = lookupWeird xs i
lookupWeird (consT x xs) (T i) = lookupWeird xs i

deBruijnifyC : RawTermCon → TermCon
deBruijnifyC (integer i) = integer i
deBruijnifyC (bytestring b) = bytestring b
deBruijnifyC (string x) = string x

deBruijnifyTm : ∀{n}{w : Weirdℕ n} → WeirdVec String w → RawTm → Maybe (ScopedTm w)
deBruijnifyTm g (` x) = map ` (velemIndexWeird x g)
deBruijnifyTm g (ƛ x A L) = do
  A ← deBruijnifyTy ∥ g ∥Vec A
  L ← deBruijnifyTm (consS x g) L
  return (ƛ x A L)
deBruijnifyTm g (L · M) = do
  L ← deBruijnifyTm g L
  M ← deBruijnifyTm g M
  return (L · M)
deBruijnifyTm g (Λ x K L) =
  map (Λ x (deBruijnifyK K)) (deBruijnifyTm (consT x g) L)
deBruijnifyTm g (L ·⋆ A) = do
  L ← deBruijnifyTm g L
  A ← deBruijnifyTy ∥ g ∥Vec A
  return (L ·⋆ A)
deBruijnifyTm g (con t) = just (con (deBruijnifyC t))
deBruijnifyTm g (error A) = map error (deBruijnifyTy ∥ g ∥Vec A)
deBruijnifyTm g (builtin b) = just (builtin b [] [])
deBruijnifyTm g (wrap A B t) = do
  A ← deBruijnifyTy ∥ g ∥Vec A
  B ← deBruijnifyTy ∥ g ∥Vec B
  t ← deBruijnifyTm g t
  return (wrap A B t)
deBruijnifyTm g (unwrap t) =  do
  t ← deBruijnifyTm g t
  return (unwrap t)

--{-# COMPILE GHC deBruijnifyTm as deBruijnifyTm #-}

\end{code}

-- SATURATION OF BUILTINS


\begin{code}
open import Data.Product
open import Data.Sum

builtinMatcher : ∀{n}{w : Weirdℕ n} → ScopedTm w → (Builtin × List (ScopedTy n) × List (ScopedTm w)) ⊎ ScopedTm w
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

arity⋆ : Builtin → ℕ
arity⋆ addInteger = 1
arity⋆ subtractInteger = 1
arity⋆ multiplyInteger = 1
arity⋆ divideInteger = 1
arity⋆ quotientInteger = 1
arity⋆ remainderInteger = 1
arity⋆ modInteger = 1
arity⋆ lessThanInteger = 1
arity⋆ lessThanEqualsInteger = 1
arity⋆ greaterThanInteger = 1
arity⋆ greaterThanEqualsInteger = 1
arity⋆ equalsInteger = 1
arity⋆ concatenate = 1
arity⋆ takeByteString = 2
arity⋆ dropByteString = 2
arity⋆ sha2-256 = 1
arity⋆ sha3-256 = 1
arity⋆ verifySignature = 3
arity⋆ equalsByteString = 1

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
saturate (Λ x K t)        = Λ x K (saturate t)
saturate (t ·⋆ A)       with builtinMatcher (saturate t)
saturate (t ·⋆ A) | inj₁ (b , As , ts) = builtinEater⋆ b As ts A
saturate (t ·⋆ A) | inj₂ t'            = t' ·⋆ A
saturate (ƛ x A t)        = ƛ x A (saturate t)
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
unsaturate (Λ x K t) = Λ x K (unsaturate t)
unsaturate (t ·⋆ A) = unsaturate t ·⋆ A
unsaturate (ƛ x A t) = ƛ x A (unsaturate t)
unsaturate (t · u) = unsaturate t · unsaturate u
unsaturate (con c) = con c
unsaturate (error A) = error A
unsaturate (builtin b As bs) =
  builtinBuilder b (Data.List.reverse As) (Data.List.reverse bs)
unsaturate (wrap A B t) = wrap A B (unsaturate t)
unsaturate (unwrap t)   = unwrap (unsaturate t)
\end{code}

\begin{code}
unDeBruijnifyK : ScopedKind → RawKind
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
unDeBruijnifyC (integer i) = integer i
unDeBruijnifyC (bytestring b) = bytestring b
unDeBruijnifyC (string x) = string x
  \end{code}

\begin{code}
unDeBruijnify⋆ : ∀{n} → ℕ → ScopedTy n → RawTy
unDeBruijnify⋆ i (` x) = ` ("tvar" ++ Data.Integer.show (ℤ.pos i - ℤ.pos (ℕ.suc (toℕ x))))
unDeBruijnify⋆ i (A ⇒ B) = unDeBruijnify⋆ i A ⇒ unDeBruijnify⋆ i B
unDeBruijnify⋆ i (Π x K A) = Π
  ("tvar" ++ Data.Integer.show (ℤ.pos i))
  (unDeBruijnifyK K)
  (unDeBruijnify⋆ (ℕ.suc i) A)
unDeBruijnify⋆ i (ƛ x K A) = ƛ
  ("tvar" ++ Data.Integer.show (ℤ.pos i))
  (unDeBruijnifyK K)
  (unDeBruijnify⋆ (ℕ.suc i) A)
unDeBruijnify⋆ i (A · B) = unDeBruijnify⋆ i A · unDeBruijnify⋆ i B
unDeBruijnify⋆ i (con c) = con c
unDeBruijnify⋆ i (μ A B) = μ (unDeBruijnify⋆ i A) (unDeBruijnify⋆ i B)
\end{code}

This should be run on unsaturated terms
\begin{code}
unDeBruijnify : ∀{n}{w : Weirdℕ n} →  ∀ n' → Weirdℕ n' → ScopedTm w → RawTm
unDeBruijnify i⋆ i (` x) = ` ("var" ++ Data.Integer.show (ℤ.pos (wtoℕ i) - ℤ.pos (ℕ.suc (wftoℕ x))))
unDeBruijnify i⋆ i (Λ x K t) = Λ
  ("tvar" ++ Data.Integer.show (ℤ.pos (wtoℕ i)))
  (unDeBruijnifyK K)
  (unDeBruijnify (ℕ.suc i⋆) (T i) t)
unDeBruijnify i⋆ i (t ·⋆ A) = unDeBruijnify i⋆ i t ·⋆ unDeBruijnify⋆ i⋆ A
unDeBruijnify i⋆ i (ƛ x A t) = ƛ
  ("var" ++ Data.Integer.show (ℤ.pos (wtoℕ i)))
  (unDeBruijnify⋆ i⋆ A)
  (unDeBruijnify i⋆ (S i) t)
unDeBruijnify i⋆ i (t · u) = unDeBruijnify i⋆ i t · unDeBruijnify i⋆ i u
unDeBruijnify i⋆ i (con c) = con (unDeBruijnifyC c)
unDeBruijnify i⋆ i (error A) = error (unDeBruijnify⋆ i⋆ A)
unDeBruijnify i⋆ i (builtin b _ _) = builtin b
unDeBruijnify i⋆ i (wrap A B t) =
  wrap (unDeBruijnify⋆ i⋆ A) (unDeBruijnify⋆ i⋆ B) (unDeBruijnify i⋆ i t)
unDeBruijnify i⋆ i (unwrap t) = unwrap (unDeBruijnify i⋆ i t)
\end{code}

\begin{code}
deDeBruijnify⋆ : ∀{n} → Vec String n → ScopedTy n → RawTy
deDeBruijnify⋆ xs (` x) = ` (Data.Vec.lookup xs x)
deDeBruijnify⋆ xs (t ⇒ u) = deDeBruijnify⋆ xs t ⇒ deDeBruijnify⋆ xs u
deDeBruijnify⋆ xs (Π x K t) = Π x (unDeBruijnifyK K) (deDeBruijnify⋆ (x ∷ xs) t)
deDeBruijnify⋆ xs (ƛ x K t) = ƛ x (unDeBruijnifyK K) (deDeBruijnify⋆ (x ∷ xs) t)
deDeBruijnify⋆ xs (t · u) = deDeBruijnify⋆ xs t · deDeBruijnify⋆ xs u
deDeBruijnify⋆ xs (con x) = con x
deDeBruijnify⋆ xs (μ t u) = μ (deDeBruijnify⋆ xs t) (deDeBruijnify⋆ xs u)

deDeBruijnify : ∀{n}{w : Weirdℕ n} → Vec String n → WeirdVec String w → ScopedTm w → RawTm
deDeBruijnify xs⋆ xs (` x) = ` (lookupWeird xs x)
deDeBruijnify xs⋆ xs (Λ x K t) = Λ x (unDeBruijnifyK K) (deDeBruijnify (x ∷ xs⋆) (consT x xs) t) -- surprised x goes on both
deDeBruijnify xs⋆ xs (t ·⋆ A) = deDeBruijnify xs⋆ xs t ·⋆ deDeBruijnify⋆ xs⋆ A
deDeBruijnify xs⋆ xs (ƛ x A t) = ƛ x (deDeBruijnify⋆ xs⋆ A) (deDeBruijnify xs⋆ (consS x xs) t)
deDeBruijnify xs⋆ xs (t · u) = deDeBruijnify xs⋆ xs t · deDeBruijnify xs⋆ xs u
deDeBruijnify xs⋆ xs (con x) = con (unDeBruijnifyC x)
deDeBruijnify xs⋆ xs (error x) = error (deDeBruijnify⋆ xs⋆ x)
deDeBruijnify xs⋆ xs (builtin x _ _) = builtin x
deDeBruijnify xs⋆ xs (wrap A B t) = wrap (deDeBruijnify⋆ xs⋆ A) (deDeBruijnify⋆ xs⋆ B) (deDeBruijnify xs⋆ xs t)
deDeBruijnify xs⋆ xs (unwrap t) = unwrap (deDeBruijnify xs⋆ xs t)

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
ugly (ƛ x _ t) = "(ƛ " ++ ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (Λ x _ t) = "(Λ " ++ ugly t ++ ")"
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
