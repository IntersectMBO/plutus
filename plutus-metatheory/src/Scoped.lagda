\begin{code}
module Scoped where
\end{code}

\begin{code}
open import Data.Nat using (ℕ;zero;suc;∣_-_∣)
open import Data.Fin using (Fin;zero;suc;toℕ) 
open import Data.Integer.Show using () renaming (show to ishow)
open import Data.Vec using (Vec;[];_∷_)
open import Data.Bool using (Bool)
open import Data.Product using (_×_;_,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl)
open import Data.Sum using (_⊎_;inj₁)
open import Data.String using (String;_++_)

open import Builtin using (Builtin)
open Builtin.Builtin

open import Builtin.Signature using (_⊢♯;integer;bytestring) 
open import Builtin.Constant.Type
open import Builtin.Constant.AtomicType using (aBool)

open import Raw using (RawTy;RawTm;RawTyCon)
open RawTy
open RawTm
open RawTyCon

open import Utils using (Kind;Maybe;nothing;just;maybe;Monad;Either;inj₁;inj₂;List;[];_∷_)
open Monad{{...}}

open import RawU using (TyTag;TmCon;tmCon;tagCon2TmCon;tmCon2TagCon)
\end{code}

\begin{code}
data ScopedTy (n : ℕ) : Set where
  `    : Fin n → ScopedTy n
  _⇒_  : ScopedTy n → ScopedTy n → ScopedTy n
  Π    : Kind → ScopedTy (suc n) → ScopedTy n
  ƛ    : Kind → ScopedTy (suc n) → ScopedTy n
  _·_  : ScopedTy n → ScopedTy n → ScopedTy n
  con  : ∀{K} → TyCon K → ScopedTy n
  μ    : ScopedTy n → ScopedTy n → ScopedTy n
  SOP  : List (List (ScopedTy n)) → ScopedTy n

Tel⋆ : ℕ → ℕ → Set
Tel⋆ n m = Vec (ScopedTy n) m

-- contexts

data Weirdℕ : ℕ → Set where
  Z : Weirdℕ 0
  S : ∀{n} → Weirdℕ n  → Weirdℕ n
  T : ∀{n} → Weirdℕ n → Weirdℕ (suc n)

-- variables

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
shifterTyList : ∀{n}(w : Weirdℕ n) → List RawTy → List RawTy
shifterTyListList : ∀{n}(w : Weirdℕ n) → List (List RawTy) → List (List RawTy)

shifterTy w (` x)     = ` (maybe (\x → x) 100 (lookupWTy ∣ x - 1 ∣  w))
shifterTy w (A ⇒ B)   = shifterTy w A ⇒ shifterTy w B
shifterTy w (Π K A)   = Π K (shifterTy (T w) A)
shifterTy w (ƛ K A)   = ƛ K (shifterTy (T w) A)
shifterTy w (A · B)   = shifterTy w A · shifterTy w B
shifterTy w (con c)   = con c
shifterTy w (μ A B)   = μ (shifterTy w A) (shifterTy w B)
shifterTy w (SOP tss) = SOP (shifterTyListList w tss)

shifterTyList w [] = []
shifterTyList w (x ∷ xs) = shifterTy w x ∷ shifterTyList w xs

shifterTyListList w [] = []
shifterTyListList w (xs ∷ xss) = shifterTyList w xs ∷ shifterTyListList w xss

shifter : ∀{n}(w : Weirdℕ n) → RawTm → RawTm
shifterList : ∀{n}(w : Weirdℕ n) → List RawTm → List RawTm

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
shifter w (constr A i cs) = constr (shifterTy w A) i (shifterList w cs)
shifter w (case A x cs) = case (shifterTy w A) (shifter w x) (shifterList w cs)

shifterList w [] = []
shifterList w (x ∷ xs) = shifter w x ∷ shifterList w xs

unshifterTy : ∀{n} → Weirdℕ n → RawTy → RawTy
unshifterTyList : ∀{n}(w : Weirdℕ n) → List RawTy → List RawTy
unshifterTyListList : ∀{n}(w : Weirdℕ n) → List (List RawTy) → List (List RawTy)

unshifterTy w (` x)     = ` (lookupWTy' x w)
unshifterTy w (A ⇒ B)   = unshifterTy w A ⇒ unshifterTy w B
unshifterTy w (Π K A)   = Π K (unshifterTy (T w) A)
unshifterTy w (ƛ K A)   = ƛ K (unshifterTy (T w) A)
unshifterTy w (A · B)   = unshifterTy w A · unshifterTy w B
unshifterTy w (con c)   = con c
unshifterTy w (μ A B)   = μ (unshifterTy w A) (unshifterTy w B)
unshifterTy w (SOP tss) = SOP (unshifterTyListList w tss)

unshifterTyList w [] = []
unshifterTyList w (x ∷ xs) = unshifterTy w x ∷ unshifterTyList w xs

unshifterTyListList w [] = []
unshifterTyListList w (xs ∷ xss) = unshifterTyList w xs ∷ unshifterTyListList w xss

unshifter : ∀{n} → Weirdℕ n → RawTm → RawTm
unshifterList : ∀{n}(w : Weirdℕ n) → List RawTm → List RawTm

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
unshifter w (constr A i cs) = constr (unshifterTy w A) i (unshifterList w cs)
unshifter w (case A t cs) = case (unshifterTy w A) (unshifter w t) (unshifterList w cs)

unshifterList w [] = []
unshifterList w (x ∷ xs) = unshifter w x ∷ unshifterList w xs

data ScopedTm {n}(w : Weirdℕ n) : Set where
  `    :    WeirdFin w → ScopedTm w
  Λ    :    Kind → ScopedTm (T w) → ScopedTm w
  _·⋆_ :    ScopedTm w → ScopedTy n → ScopedTm w
  ƛ    :    ScopedTy n → ScopedTm (S w) → ScopedTm w
  _·_  :    ScopedTm w → ScopedTm w → ScopedTm w
  con  :    TmCon → ScopedTm w
  error :   ScopedTy n → ScopedTm w
  builtin : (b : Builtin) → ScopedTm w
  wrap :    ScopedTy n → ScopedTy n → ScopedTm w → ScopedTm w
  unwrap :  ScopedTm w → ScopedTm w
  constr        : (A : ScopedTy n) → (i : ℕ) → (cs : List (ScopedTm w)) → ScopedTm w
  case          : (A : ScopedTy n) → (arg : ScopedTm w) → (cs : List (ScopedTm w)) → ScopedTm w

Tel : ∀{n} → Weirdℕ n → ℕ → Set
Tel w n = Vec (ScopedTm w) n

-- SCOPE CHECKING / CONVERSION FROM RAW TO SCOPED

-- should just use ordinary kind for everything

postulate
  FreeVariableError : Set

{-# COMPILE GHC FreeVariableError = type FreeVariableError #-}


data ScopeError : Set where
  deBError : ScopeError
  freeVariableError : FreeVariableError → ScopeError

{-# FOREIGN GHC import PlutusCore.DeBruijn #-}
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
scopeCheckTyList : ∀{n} → List RawTy → Either ScopeError (List (ScopedTy n))
scopeCheckTyListList : ∀{n} → List (List RawTy) → Either ScopeError (List (List (ScopedTy n)))

scopeCheckTy (` x) = fmap ` (ℕtoFin x)
scopeCheckTy (A ⇒ B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A ⇒ B)
scopeCheckTy (Π K A) = fmap (Π K) (scopeCheckTy A)
scopeCheckTy (ƛ K A) = fmap (ƛ K) (scopeCheckTy A)
scopeCheckTy (A · B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (A · B)
scopeCheckTy (con (atomic x)) = return (con (atomic x))
scopeCheckTy (con list) = return (con list)
scopeCheckTy (con pair) = return (con pair)
scopeCheckTy (μ A B) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  return (μ A B)
scopeCheckTy (SOP xss) = do 
      A ← scopeCheckTyListList xss  
      return (SOP A)

scopeCheckTyList [] = return []
scopeCheckTyList (x ∷ xs) = do 
      A  ← scopeCheckTy x 
      AS ← scopeCheckTyList xs
      return (A ∷ AS)

scopeCheckTyListList [] = return []
scopeCheckTyListList (xs ∷ xss) = do 
      AS  ← scopeCheckTyList xs 
      ASS ← scopeCheckTyListList xss
      return (AS ∷ ASS)

scopeCheckTm : ∀{n}{w : Weirdℕ n} → RawTm → Either ScopeError (ScopedTm w)
scopeCheckTmList : ∀{n}{w : Weirdℕ n} → List RawTm → Either ScopeError (List (ScopedTm w))

scopeCheckTm (` x) = fmap ` (ℕtoWeirdFin x)
scopeCheckTm {n}{w}(Λ K t) = fmap (Λ K) (scopeCheckTm {suc n}{T w} t)
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
scopeCheckTm (con c) = return (con (tagCon2TmCon c))
scopeCheckTm (builtin b) = return (builtin b)
scopeCheckTm (error A) = fmap error (scopeCheckTy A)
scopeCheckTm (wrap A B t) = do
  A ← scopeCheckTy A
  B ← scopeCheckTy B
  t ← scopeCheckTm t
  return (wrap A B t)
scopeCheckTm (unwrap t) = fmap unwrap (scopeCheckTm t)
scopeCheckTm (constr A i cs) = do 
  A  ← scopeCheckTy A 
  cs ← scopeCheckTmList cs
  return (constr A i cs)
scopeCheckTm (case A t cs) = do 
  A  ← scopeCheckTy A
  t  ← scopeCheckTm t
  cs ← scopeCheckTmList cs
  return (case A t cs)

scopeCheckTmList [] = return []
scopeCheckTmList (x ∷ xs) = do 
  x  ← scopeCheckTm x 
  xs ← scopeCheckTmList xs 
  return (x ∷ xs)
\end{code}

\begin{code}
extricateScopeTy : ∀{n} → ScopedTy n → RawTy
extricateScopeTyList : ∀{n} → List (ScopedTy n) → List RawTy
extricateScopeTyListList : ∀{n} → List (List (ScopedTy n)) → List (List RawTy)

extricateScopeTy (` x)      = ` (toℕ x)
extricateScopeTy (A ⇒ B)    = extricateScopeTy A ⇒ extricateScopeTy B
extricateScopeTy (Π K A)    = Π K (extricateScopeTy A)
extricateScopeTy (ƛ K A)    = ƛ K (extricateScopeTy A)
extricateScopeTy (A · B)    = extricateScopeTy A · extricateScopeTy B
extricateScopeTy (con (atomic x)) = con (atomic x)
extricateScopeTy (con list) = con list
extricateScopeTy (con pair) = con pair
extricateScopeTy (μ A B)    = μ (extricateScopeTy A) (extricateScopeTy B)
extricateScopeTy (SOP tss)  = SOP (extricateScopeTyListList tss)

extricateScopeTyList [] = []
extricateScopeTyList (x ∷ xs) = extricateScopeTy x ∷ extricateScopeTyList xs

extricateScopeTyListList [] = []
extricateScopeTyListList (xs ∷ xss) = extricateScopeTyList xs ∷ extricateScopeTyListList xss

extricateScope : ∀{n}{w : Weirdℕ n} → ScopedTm w → RawTm
extricateScopeList  : ∀{n}{w : Weirdℕ n} → List (ScopedTm w) → List RawTm

extricateScope (` x) = ` (WeirdFintoℕ x)
extricateScope (Λ K t) = Λ K (extricateScope t)
extricateScope (t ·⋆ A) = extricateScope t ·⋆ extricateScopeTy A
extricateScope (ƛ A t) = ƛ (extricateScopeTy A) (extricateScope t)
extricateScope (t · u) = extricateScope t · extricateScope u
extricateScope (con c) = con (tmCon2TagCon c)
extricateScope (error A) = error (extricateScopeTy A)
extricateScope (builtin bn) = builtin bn
extricateScope (wrap pat arg t) =
  wrap (extricateScopeTy pat) (extricateScopeTy arg) (extricateScope t)
extricateScope (unwrap t) = unwrap (extricateScope t)
extricateScope (constr A i cs) = constr (extricateScopeTy A) i (extricateScopeList cs)
extricateScope (case A x cs) = case (extricateScopeTy A) (extricateScope x) (extricateScopeList cs)

extricateScopeList [] = []
extricateScopeList (x ∷ xs) = extricateScope x ∷ extricateScopeList xs
\end{code}

-- UGLY PRINTING

\begin{code}
uglyWeirdFin : ∀{n}{w : Weirdℕ n} → WeirdFin w → String
uglyWeirdFin Z = "0"
uglyWeirdFin (T x) = "(T " ++ uglyWeirdFin x ++ ")"
uglyWeirdFin (S x) = "(S " ++ uglyWeirdFin x ++ ")"

uglyTmCon : TmCon → String
uglyTmCon (tmCon integer x) = "(integer " ++ ishow x ++ ")"
uglyTmCon (tmCon bytestring x) = "bytestring"
uglyTmCon size = "size"


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
ugly (builtin b) = "builtin " ++ uglyBuiltin b
{-  "(builtin " ++
  uglyBuiltin b ++
  " " ++
  ishow (Data.Integer.ℤ.pos (Data.List.length As)) ++
  " " ++
  ishow (Data.Integer.ℤ.pos (Data.List.length ts))
  ++ ")" -}
ugly (error _) = "error _"
ugly (wrap _ _ t) = "(wrap " ++ ugly t ++ ")"
ugly (unwrap t) = "(unwrap " ++ ugly t ++ ")"
ugly (constr A i cs) = "constr" -- TODO: Do it better
ugly (case A x cs)   = "case"   -- TODO: Do it better
\end{code}
