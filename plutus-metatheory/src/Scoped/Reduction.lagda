\begin{code}
module Scoped.Reduction where
\end{code}

\begin{code}
open import Scoped
open import Scoped.RenamingSubstitution
open import Builtin
open import Builtin.Constant.Type

open import Utils

open import Agda.Builtin.String using (primStringFromList; primStringAppend)
import Data.List as List
open import Data.Sum renaming (inj₁ to inl; inj₂ to inr)
open import Data.Vec using ([];_∷_;_++_)
open import Data.Product
open import Function
open import Data.Integer as I
open import Data.Nat as N hiding (_<?_;_>?_;_≥?_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_];trans)
open import Data.Bool using (Bool;true;false)
import Debug.Trace as Debug
\end{code}

\begin{code}
infix 2 _—→_
\end{code}

\begin{code}
data _≤W'_ {n}(w : Weirdℕ n) : ∀{n'} → Weirdℕ n' → Set where
 base : w ≤W' w
 skipT : ∀{n'}{w' : Weirdℕ n'} → (T w) ≤W' w' → w ≤W' w'
 skipS : ∀{n'}{w' : Weirdℕ n'} → (S w) ≤W' w' → w ≤W' w'

-- the number of arguments for builtin, type arguments and then term
-- arguments type arguments and term arguments can be interspersed
ISIG : Builtin → Σ ℕ λ n → Weirdℕ n
ISIG addInteger = 0 , S (S Z)
ISIG subtractInteger = 0 , S (S Z)
ISIG multiplyInteger = 0 , S (S Z)
ISIG divideInteger = 0 , S (S Z)
ISIG quotientInteger = 0 , S (S Z)
ISIG remainderInteger = 0 , S (S Z)
ISIG modInteger = 0 , S (S Z)
ISIG lessThanInteger = 0 , S (S Z)
ISIG lessThanEqualsInteger = 0 , S (S Z)
ISIG greaterThanInteger = 0 , S (S Z)
ISIG greaterThanEqualsInteger = 0 , S (S Z)
ISIG equalsInteger = 0 , S (S Z)
ISIG concatenate = 0 , S (S Z)
ISIG takeByteString = 0 , S (S Z)
ISIG dropByteString = 0 , S (S Z)
ISIG lessThanByteString = 0 , S (S Z)
ISIG greaterThanByteString = 0 , S (S Z)
ISIG sha2-256 = 0 , S Z
ISIG sha3-256 = 0 , S Z
ISIG verifySignature = 0 , S (S (S Z))
ISIG equalsByteString = 0 , S (S Z)
ISIG ifThenElse = 1 , S (S (S (T Z))) -- this may be in the wrong order
ISIG charToString = 0 , S (S Z)
ISIG append = 0 , S (S Z)
ISIG trace = 0 , S Z

open import Data.Unit
ITel : Builtin → ∀{n n'}(w : Weirdℕ n)(w' : Weirdℕ n') → Set

data Value {n}{w : Weirdℕ n} : ScopedTm w → Set where
  V-ƛ : ∀ (A : ScopedTy n)(t : ScopedTm (S w)) → Value (ƛ A t)
  V-Λ : ∀ {K}(t : ScopedTm (T w)) → Value (Λ K t)
  V-con : (tcn : TermCon) → Value (con {n} tcn)
  V-wrap : (A B : ScopedTy n){t : ScopedTm w} → Value t → Value (wrap A B t)
  V-builtin : (b : Builtin)
            → (t : ScopedTm w)
            → ∀{m m'}{v : Weirdℕ m}{v' : Weirdℕ m'}
            -- the next arg expected is a term arg
            → let m'' , v'' = ISIG b in
              (p : m'' ≡ m')
            → (q : subst Weirdℕ p v'' ≡ v')
            → S v ≤W' v'
            → ITel b v w
            → Value t
  V-builtin⋆ : (b : Builtin)
             → (t : ScopedTm w)
            → ∀{m m'}{v : Weirdℕ m}{v' : Weirdℕ m'}
            -- the next arg expected is a type arg
            → let m'' , v'' = ISIG b in
              (p : m'' ≡ m')
            → (q : subst Weirdℕ p v'' ≡ v')
            → T v ≤W' v'
            → ITel b v w
            → Value t

ITel b Z     w' = ⊤
ITel b (S w) w' = ITel b w w' × Σ (ScopedTm w') Value
ITel b (T w) w' = ITel b w w'

voidVal : ∀ {n}(w : Weirdℕ n) → Value {w = w} (con unit)
voidVal w = V-con {w = w} unit

deval : ∀{n}{w : Weirdℕ n}{t : ScopedTm w} → Value t → ScopedTm w
deval {t = t} v = t

-- a term that satisfies this predicate has an error term in it somewhere
-- or we encountered a rumtime type error
data Error {n}{w : Weirdℕ n} : ScopedTm w → Set where
   -- a genuine runtime error returned from a builtin
   E-error : (A : ScopedTy n) → Error (error A)

data Any {n : ℕ}{w : Weirdℕ n}(P : ScopedTm w → Set) : ∀{m} → Tel w m → Set
  where
  here  : ∀{m t}{ts : Tel w m} → P t → Any P (t ∷ ts)
  there : ∀{m t}{ts : Tel w m} → Value t → Any P ts → Any P (t ∷ ts)

VERIFYSIG : ∀{n}{w : Weirdℕ n} → Maybe Bool → ScopedTm w
VERIFYSIG (just false) = con (bool false)
VERIFYSIG (just true)  = con (bool true)
VERIFYSIG nothing      = error (con bool)

open import Data.List using (List;[];_∷_)
open import Type using (Kind)

IBUILTIN : ∀{n}{w : Weirdℕ n}(b : Builtin) → ITel b (proj₂ (ISIG b)) w → ScopedTm w
IBUILTIN addInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = con (integer (i I.+ i'))
IBUILTIN subtractInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = con (integer (i I.- i'))
IBUILTIN multiplyInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = con (integer (i I.* i'))
IBUILTIN divideInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (div i i')))
IBUILTIN quotientInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (quot i i')))
IBUILTIN remainderInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (rem i i')))
IBUILTIN modInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (∣ i' ∣ N.≟ 0) (error (con integer)) (con (integer (mod i i')))
IBUILTIN lessThanInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (i I.<? i') (con (bool true)) (con (bool false))
IBUILTIN lessThanEqualsInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (i I.≤? i') (con (bool true)) (con (bool false))
IBUILTIN greaterThanInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (i I>? i') (con (bool true)) (con (bool false))
IBUILTIN greaterThanEqualsInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (i I≥? i') (con (bool true)) (con (bool false))
IBUILTIN equalsInteger ((_ , t , V-con (integer i)) , t' , V-con (integer i')) = decIf (i I.≟ i') (con (bool true)) (con (bool false))
IBUILTIN concatenate ((_ , t , V-con (bytestring b)) , t' , V-con (bytestring b')) = con (bool (equals b b')) 
IBUILTIN takeByteString ((_ , t , V-con (integer i)) , t' , V-con (bytestring b)) = con (bytestring (take i b)) 
IBUILTIN dropByteString ((_ , t , V-con (integer i)) , t' , V-con (bytestring b)) = con (bytestring (drop i b)) 
IBUILTIN sha2-256 (_ , t , V-con (bytestring b)) = con (bytestring (SHA2-256 b))
IBUILTIN sha3-256 (_ , t , V-con (bytestring b)) = con (bytestring (SHA3-256 b))
IBUILTIN verifySignature (((_ , t , V-con (bytestring k)) , t' , V-con (bytestring d)) , t'' , V-con (bytestring c)) = VERIFYSIG (verifySig k d c)
IBUILTIN equalsByteString  ((_ , t , V-con (bytestring b)) , t' , V-con (bytestring b')) = con (bool (equals b b'))
IBUILTIN ifThenElse (((_ , _ , V-con (bool true))  , t , _) , f , _) = t
IBUILTIN ifThenElse (((_ , _ , V-con (bool false)) , t , _) , f , _) = f
IBUILTIN charToString (_ , t , V-con (char c)) =
  con (string (primStringFromList (c ∷ [])))
IBUILTIN append ((_ , t , V-con (string s)) , t' , V-con (string s')) =
  con (string (primStringAppend s s'))
IBUILTIN trace (_ , t , V-con (string s)) = con (Debug.trace s unit)
IBUILTIN _ _ = error missing

IBUILTIN' : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}(b : Builtin) → (p : proj₁ (ISIG b) ≡ n') → subst Weirdℕ p (proj₂ (ISIG b)) ≡ w' → ITel b w' w → ScopedTm w
IBUILTIN' b refl refl σ = IBUILTIN b σ



data _—→_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  ξ-·₁ : {L L' M : ScopedTm w} → L —→ L' → L · M —→ L' · M
  ξ-·₂ : {L M M' : ScopedTm w} → Value L → M —→ M' → L · M —→ L · M'
  ξ-·⋆ : {L L' : ScopedTm w}{A : ScopedTy n} → L —→ L' → L ·⋆ A —→ L' ·⋆ A
  ξ-wrap : {A B : ScopedTy n}{L L' : ScopedTm w}
    → L —→ L' → wrap A B L —→ wrap A B L'
  β-ƛ : ∀{A : ScopedTy n}{L : ScopedTm (S w)}{M : ScopedTm w} → Value M
      → (ƛ A L) · M —→ (L [ M ])
  β-Λ : ∀{K}{L : ScopedTm (T w)}{A : ScopedTy n}
      → (Λ K L) ·⋆ A —→ (L [ A ]⋆)
  ξ-unwrap : {t t' : ScopedTm w} → t —→ t' → unwrap t —→ unwrap t'
  β-wrap : {A B : ScopedTy n}{t : ScopedTm w}
    → Value t → unwrap (wrap A B t) —→ t

  β-builtin : (b : Builtin)
            → (t u : ScopedTm w)
            → ∀{m}{v : Weirdℕ m}
            -- the next arg expected is a term arg
            → let m' , v' = ISIG b in
              (p : m' ≡ m)
            → (q : subst Weirdℕ p v' ≡ S v)
            → (σ : ITel b v w)
            → (V : Value u)
            → t · u —→ IBUILTIN' b p q (σ , u , V)

  β-builtin⋆ : (b : Builtin)
            → (t : ScopedTm w)
            → (A : ScopedTy n)
            → ∀{m}{v : Weirdℕ m}
            -- the next arg expected is a term arg
            → let m' , v' = ISIG b in
              (p : m' ≡ ℕ.suc m)
            → (q : subst Weirdℕ p v' ≡ T v)
            → (σ : ITel b v w)
            → t ·⋆ A —→ IBUILTIN' b p q σ

  E-·₁ : {A : ScopedTy n}{M : ScopedTm w} → error A · M —→ error missing
  E-·₂ : {A : ScopedTy n}{L : ScopedTm w} → Value L → L · error A —→ error missing

  -- error inside somewhere

  E-·⋆ : {A B : ScopedTy n} → error A ·⋆ B —→ error missing
--  E-Λ : ∀{K}{A : ScopedTy (N.suc n)} → Λ K (error A) —→ error missing

  E-unwrap : {A : ScopedTy n}
    → unwrap (error A) —→ error missing
  E-wrap : {A B C : ScopedTy n}
    → wrap A B (error C) —→ error missing

  -- runtime type errors
  -- these couldn't happen in the intrinsically typed version
  E-Λ·    : ∀{K}{L : ScopedTm (T w)}{M : ScopedTm w}
    → Λ K L · M —→ error missing
  E-ƛ·⋆   : ∀{B : ScopedTy n}{L : ScopedTm (S w)}{A : ScopedTy n}
    → ƛ B L ·⋆ A —→ error missing
  E-con·  : ∀{tcn}{M : ScopedTm w} → con tcn · M —→ error missing
  E-con·⋆ : ∀{tcn}{A : ScopedTy n} → con tcn ·⋆ A —→ error missing
  E-wrap· : {A B : ScopedTy n}{t M : ScopedTm w}
    → wrap A B t · M —→ error missing
  E-wrap·⋆ : {A' B A : ScopedTy n}{t : ScopedTm w}
    → wrap A' B t ·⋆ A —→ error missing
  E-ƛunwrap : {A : ScopedTy n}{t : ScopedTm (S w)}
    → unwrap (ƛ A t) —→ error missing
  E-Λunwrap : ∀{K}{t : ScopedTm (T w)} → unwrap (Λ K t) —→ error missing
  E-conunwrap : ∀{tcn} → unwrap (con tcn) —→ error missing

  E-builtin⋆· : ∀{t u : ScopedTm w} → t · u —→ error missing
  E-builtin·⋆ : ∀{t : ScopedTm w}{A} → t ·⋆ A —→ error missing
  E-builtinunwrap : ∀{t : ScopedTm w} → unwrap t —→ error missing
  E-builtin⋆unwrap : ∀{t : ScopedTm w} → unwrap t —→ error missing
\end{code}

\begin{code}
data _—→⋆_ {n}{w : Weirdℕ n} : ScopedTm w → ScopedTm w → Set where
  refl  : {t : ScopedTm w} → t —→⋆ t
  trans : {t t' t'' : ScopedTm w} → t —→ t' → t' —→⋆ t'' → t —→⋆ t''
\end{code}

\begin{code}
data Progress {n}{i : Weirdℕ n}(t : ScopedTm i) : Set where
  step : ∀{t'} → t —→ t' → Progress t
  done : Value t → Progress t
  error : Error t → Progress t
\end{code}

\begin{code}
progress·V : ∀{n}{i : Weirdℕ n}
  → {t : ScopedTm i} → Value t
  → {u : ScopedTm i} → Progress u
  → Progress (t · u)
progress·V v                        (step q)            = step (ξ-·₂ v q)
progress·V v                        (error (E-error A)) = step (E-·₂ v)
progress·V (V-ƛ A t)                (done v)            = step (β-ƛ v)
progress·V (V-Λ p)                  (done v)            = step E-Λ·
progress·V (V-con tcn)              (done v)            = step E-con·
progress·V (V-wrap A B t)           (done v)            = step E-wrap·
progress·V (V-builtin⋆ b t p q r σ) (done v)            = step E-builtin⋆·
progress·V (V-builtin b t p q base σ) (done v) =
  step (β-builtin b t (deval v) p q σ v)
progress·V (V-builtin b t p q (skipT r) σ) (done v) = done (V-builtin⋆ b (t · deval v) p q r (σ , deval v , v))
progress·V (V-builtin b t p q (skipS r) σ) (done v) = done (V-builtin b (t · deval v) p q r (σ , deval v , v))

progress· : ∀{n}{i : Weirdℕ n}
  → {t : ScopedTm i} → Progress t
  → {u : ScopedTm i} → Progress u
  → Progress (t · u)
progress· (done v)            q = progress·V v q
progress· (step p)            q = step (ξ-·₁ p)
progress· (error (E-error A)) q = step E-·₁

progress·⋆ : ∀{n}{i : Weirdℕ n}{t : ScopedTm i}
  → Progress t → (A : ScopedTy n) → Progress (t ·⋆ A)
progress·⋆ (step p)                     A = step (ξ-·⋆ p)
progress·⋆ (done (V-ƛ B t))             A = step E-ƛ·⋆
progress·⋆ (done (V-Λ p))               A = step β-Λ
progress·⋆ (done (V-con tcn))           A = step E-con·⋆
progress·⋆ (done (V-wrap pat arg t))    A = step E-wrap·⋆
progress·⋆ (done (V-builtin⋆ b t p q base σ)) A = step (β-builtin⋆ b t A p q σ)
progress·⋆ (done (V-builtin⋆ b t p q (skipT r) σ)) A = done (V-builtin⋆ b (t ·⋆ A) p q r σ)
progress·⋆ (done (V-builtin⋆ b t p q (skipS r) σ)) A = done (V-builtin b (t ·⋆ A) p q r σ)
progress·⋆ (done (V-builtin b t p q r s)) A = step E-builtin·⋆

progress·⋆ (error (E-error A))          B = step E-·⋆

progress-unwrap : ∀{n}{i : Weirdℕ n}{t : ScopedTm i}
  → Progress t → Progress (unwrap t)
progress-unwrap (step p)                        = step (ξ-unwrap p)
progress-unwrap (done (V-ƛ A t))                = step E-ƛunwrap
progress-unwrap (done (V-Λ p))                  = step E-Λunwrap
progress-unwrap (done (V-con tcn))              = step E-conunwrap
progress-unwrap (done (V-wrap A B v))           = step (β-wrap v)
progress-unwrap (done (V-builtin b t p q r σ))  = step E-builtinunwrap
progress-unwrap (done (V-builtin⋆ b t p q r σ)) = step E-builtin⋆unwrap
progress-unwrap (error (E-error A))             = step E-unwrap

ival : ∀ b → Value {w = Z} (ibuiltin b)
ival addInteger = V-builtin addInteger _ refl refl (skipS base) _
ival subtractInteger = V-builtin subtractInteger _ refl refl (skipS base) _
ival multiplyInteger = V-builtin multiplyInteger _ refl refl (skipS base) _
ival divideInteger = V-builtin divideInteger _ refl refl (skipS base) _
ival quotientInteger = V-builtin quotientInteger _ refl refl (skipS base) _
ival remainderInteger = V-builtin remainderInteger _ refl refl (skipS base) _
ival modInteger = V-builtin modInteger _ refl refl (skipS base) _
ival lessThanInteger = V-builtin lessThanInteger _ refl refl (skipS base) _
ival lessThanEqualsInteger = V-builtin lessThanEqualsInteger _ refl refl (skipS base) _
ival greaterThanInteger = V-builtin greaterThanInteger _ refl refl (skipS base) _
ival greaterThanEqualsInteger = V-builtin greaterThanEqualsInteger _ refl refl (skipS base) _
ival equalsInteger = V-builtin equalsInteger _ refl refl (skipS base) _
ival concatenate = V-builtin concatenate _ refl refl (skipS base) _
ival takeByteString = V-builtin takeByteString _ refl refl (skipS base) _
ival dropByteString = V-builtin dropByteString _ refl refl (skipS base) _
ival lessThanByteString = V-builtin equalsByteString _ refl refl (skipS base) _
ival greaterThanByteString = V-builtin equalsByteString _ refl refl (skipS base) _
ival sha2-256 = V-builtin sha2-256 _ refl refl base _
ival sha3-256 = V-builtin sha2-256 _ refl refl base _
ival verifySignature = V-builtin verifySignature _ refl refl (skipS (skipS base)) _
ival equalsByteString = V-builtin equalsByteString _ refl refl (skipS base) _
ival ifThenElse = V-builtin ifThenElse _ refl refl (skipS (skipS base)) _
ival charToString = V-builtin charToString _ refl refl (skipS base) _
ival append = V-builtin append _ refl refl (skipS base) _
ival trace = V-builtin trace _ refl refl base _

progress : (t : ScopedTm Z) → Progress t
progress (Λ K t)           = done (V-Λ t)
progress (t ·⋆ A)          = progress·⋆ (progress t) A
progress (ƛ A t)           = done (V-ƛ A t)
progress (t · u)           = progress· (progress t) (progress u)
progress (con c)           = done (V-con c)
progress (error A)         = error (E-error A)
-- type telescope is full
progress (ibuiltin b) = done (ival b)
progress (wrap A B t) with progress t
progress (wrap A B t)          | step  q           = step (ξ-wrap q)
progress (wrap A B t)          | done  q           = done (V-wrap A B q)
progress (wrap A B .(error C)) | error (E-error C) = step E-wrap
progress (unwrap t)        = progress-unwrap (progress t)
\end{code}

\begin{code}
open import Data.Nat

Steps : ScopedTm Z → Set
Steps t = Σ (ScopedTm Z) λ t' → t —→⋆ t' × (Maybe (Value t') ⊎ Error t')

run—→ : {t t' : ScopedTm Z} → t —→ t' → Steps t' → Steps t
run—→ p (t' , ps , q) = _ , ((trans p ps) , q)

run : (t : ScopedTm Z) → ℕ → Steps t
runProg : ℕ → {t : ScopedTm Z} → Progress t → Steps t

run t 0       = t , (refl , inl nothing) -- out of fuel
run t (suc n) = runProg n (progress t)

runProg n (step {t' = t'} p)  = run—→ p (run t' n)
runProg n (done V)  = _ , refl , inl (just V)
runProg n (error e) = _ , refl , inr e
\end{code}
