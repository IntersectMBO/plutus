\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ;_≟_)
open import Data.Integer using (ℤ)
open import Data.Integer.Show using (show)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Reflects;Dec;ofʸ;ofⁿ;_because_;yes;no;does)
open import Relation.Binary.PropositionalEquality using (_≡_;cong;cong₂;refl)
open import Data.Bool using (Bool;false;true;_∧_)

open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import Builtin.Constant.AtomicType using (AtomicTyCon;decAtomicTyCon)
open AtomicTyCon

open import Utils using (Kind;*;_⇒_)
open import RawU using (TagCon;tagCon;Tag;decTagCon)
open Tag
\end{code}

The raw un-scope-checked and un-type-checked syntax

\begin{code}
data RawTy : Set

data RawTyCon : Set

data RawTy where
  `   : ℕ → RawTy
  _⇒_ : RawTy → RawTy → RawTy
  Π   : Kind → RawTy → RawTy
  ƛ   : Kind → RawTy → RawTy
  _·_ : RawTy → RawTy → RawTy
  con : RawTyCon → RawTy
  μ    : RawTy → RawTy → RawTy

{-# COMPILE GHC RawTy = data RType (RTyVar | RTyFun | RTyPi | RTyLambda | RTyApp | RTyCon | RTyMu) #-}

{-# FOREIGN GHC import Raw #-}

data RawTyCon where
  atomic     : AtomicTyCon → RawTyCon
  list       : RawTy → RawTyCon
  pair       : RawTy → RawTy → RawTyCon

{-# COMPILE GHC RawTyCon = data RTyCon (RTyConAtom | RTyConList | RTyConPair) #-}

data RawTm : Set where
  `             : ℕ → RawTm
  Λ             : Kind → RawTm → RawTm
  _·⋆_          : RawTm → RawTy → RawTm
  ƛ             : RawTy → RawTm → RawTm
  _·_           : RawTm → RawTm → RawTm
  con           : TagCon → RawTm
  error         : RawTy → RawTm
  builtin       : Builtin → RawTm
  wrap          : RawTy → RawTy → RawTm → RawTm
  unwrap        : RawTm → RawTm

{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap) #-}

-- α equivalence

-- we don't have a decidable equality instance for bytestring, so I
-- converted this to bool for now

decRTy : (A A' : RawTy) → Bool

decRTyCon : (C C' : RawTyCon) → Bool
decRTyCon (atomic t) (atomic t')  = does (decAtomicTyCon t t')
decRTyCon (pair x y) (pair x' y') = decRTy x x' ∧ decRTy y y'
decRTyCon (list x)   (list x')    = decRTy x x' 
decRTyCon _          _            = false

decRKi : (K K' : Kind) → Bool
decRKi * * = true
decRKi * (K' ⇒ J') = false
decRKi (K ⇒ J) * = false
decRKi (K ⇒ J) (K' ⇒ J') = decRKi K K' ∧ decRKi J J' 

decRTy (` x) (` x') = does (x ≟ x')
decRTy (A ⇒ B) (A' ⇒ B') = decRTy A A' ∧ decRTy B B'
decRTy (Π K A) (Π K' A') = decRKi K K' ∧ decRTy A A'
decRTy (ƛ K A) (ƛ K' A') = decRKi K K' ∧ decRTy A A'
decRTy (A · B) (A' · B') = decRTy A A' ∧ decRTy B B'
decRTy (con c) (con c') = decRTyCon c c'
decRTy (μ A B) (μ A' B') = decRTy A A' ∧ decRTy B B'
decRTy _ _ = false

decRTm : (t t' : RawTm) → Bool
decRTm (` x) (` x') = does (x ≟ x')
decRTm (Λ K t) (Λ K' t') = decRKi K K' ∧ decRTm t t'
decRTm (t ·⋆ A) (t' ·⋆ A') = decRTm t t' ∧ decRTy A A'
decRTm (ƛ A t) (ƛ A' t') = decRTy A A' ∧ decRTm t t'
decRTm (t · u) (t' · u') = decRTm t t' ∧ decRTm u u'
decRTm (con c) (con c') = decTagCon c c'
decRTm (error A) (error A') = decRTy A A'
decRTm (builtin b) (builtin b') = does (decBuiltin b b')
decRTm (wrap pat ar t) (wrap pat' ar' t') = decRTy pat pat' ∧ decRTy ar ar' ∧ decRTm t t'
decRTm (unwrap t) (unwrap t') = decRTm t t'
decRTm _ _ = false

-- We have to different approaches to de Bruijn terms.
-- one counts type and term binders separately the other counts them together

rawTyPrinter : RawTy → String
rawTyPrinter (` x)   = show (ℤ.pos x)
rawTyPrinter (A ⇒ B) = "(" ++ rawTyPrinter A ++ "⇒" ++ rawTyPrinter B ++ ")"
rawTyPrinter (Π K A) = "(Π" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (ƛ K A) = "(ƛ" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (A · B) = "(" ++ rawTyPrinter A ++ "·" ++ rawTyPrinter B ++ ")"
rawTyPrinter (con c) = "(con)"
rawTyPrinter (μ A B) = "(μ" ++ rawTyPrinter A ++ rawTyPrinter B ++ ")"

rawPrinter : RawTm → String
rawPrinter (` x) = show (ℤ.pos x)
rawPrinter (Λ K t) = "(" ++ "Λ" ++ "kind" ++ rawPrinter t ++ ")"
rawPrinter (t ·⋆ A) = "(" ++ rawPrinter t ++ "·⋆" ++ rawTyPrinter A ++ ")"
rawPrinter (ƛ A t) = "(" ++ "ƛ" ++ rawTyPrinter A ++ rawPrinter t ++ ")"
rawPrinter (t · u) = "(" ++ rawPrinter t ++ "·" ++ rawPrinter u ++ ")"
rawPrinter (con c) = "(con)"
rawPrinter (error A) = "(error" ++ rawTyPrinter A ++ ")"
rawPrinter (builtin b) = "(builtin)"
rawPrinter (wrap pat ar t) = "(wrap" ++ ")"
rawPrinter (unwrap t) = "(unwrap" ++ rawPrinter t ++ ")"
\end{code}
 