\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ;_≟_)
open import Data.Integer using (ℤ)
open import Data.Integer.Show using (show)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Reflects;Dec;ofʸ;ofⁿ;_because_;yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_;cong;cong₂;refl)
open import Data.Bool using (Bool;false;true)

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
decRTyCon (atomic t) (atomic t') with decAtomicTyCon t t'
... | yes _ = true
... | no  _ = false
decRTyCon (pair x y) (pair x' y') with decRTy x x' | decRTy y y'
... | true | true   = true
... | _    | _      = false
decRTyCon (list x) (list x') with decRTy x x' 
... | false = false
... | true = true
decRTyCon _          _  = false

decRKi : (K K' : Kind) → Bool
decRKi * * = true
decRKi * (K' ⇒ J') = false
decRKi (K ⇒ J) * = false
decRKi (K ⇒ J) (K' ⇒ J') with decRKi K K'
decRKi (K ⇒ J) (K' ⇒ J') | true with decRKi J J'
decRKi (K ⇒ J) (K' ⇒ J') | true | true = true
decRKi (K ⇒ J) (K' ⇒ J') | true | false = false
decRKi (K ⇒ J) (K' ⇒ J') | false = false

decRTy (` x) (` x') with x ≟ x'
... | yes _ = true
... | no  _ = false
decRTy (` x) (A' ⇒ B') = false
decRTy (` x) (Π K' A') = false
decRTy (` x) (ƛ K' A') = false
decRTy (` x) (A' · A'') = false
decRTy (` x) (con c') = false
decRTy (` x) (μ A' B') = false
decRTy (A ⇒ B) (` x') = false
decRTy (A ⇒ B) (A' ⇒ B') with decRTy A A'
... | false = false
... | true with decRTy B B'
... | false = false
... | true = true
decRTy (A ⇒ B) (Π K' A') = false
decRTy (A ⇒ B) (ƛ K' A') = false
decRTy (A ⇒ B) (A' · A'') = false
decRTy (A ⇒ B) (con c') = false
decRTy (A ⇒ B) (μ A' B') = false
decRTy (Π K A) (` x') = false
decRTy (Π K A) (A' ⇒ B') = false
decRTy (Π K A) (Π K' A') with decRKi K K'
... | false = false
... | true with decRTy A A'
... | false = false
... | true = true
decRTy (Π K A) (ƛ K' A') = false
decRTy (Π K A) (A' · A'') = false
decRTy (Π K A) (con c') = false
decRTy (Π K A) (μ A' B') = false
decRTy (ƛ K A) (` x') = false
decRTy (ƛ K A) (A' ⇒ B') = false
decRTy (ƛ K A) (Π K' A') = false
decRTy (ƛ K A) (ƛ K' A') with decRKi K K'
... | false = false
... | true with decRTy A A'
... | false = false
... | true = true
decRTy (ƛ K A) (A' · A'') = false
decRTy (ƛ K A) (con c') = false
decRTy (ƛ K A) (μ A' B') = false
decRTy (A · B) (` x') = false
decRTy (A · B) (A' ⇒ B') = false
decRTy (A · B) (Π K' A') = false
decRTy (A · B) (ƛ K' A') = false
decRTy (A · B) (A' · B') with decRTy A A'
... | false = false
... | true with decRTy B B'
... | false = false
... | true = true
decRTy (A · B) (con c') = false
decRTy (A · B) (μ A' B') = false
decRTy (con c) (` x') = false
decRTy (con c) (A' ⇒ B') = false
decRTy (con c) (Π K' A') = false
decRTy (con c) (ƛ K' A') = false
decRTy (con c) (A' · A'') = false
decRTy (con c) (con c') with decRTyCon c c'
... | false = false
... | true = true
decRTy (con c) (μ A' B') = false
decRTy (μ A B) (` x') = false
decRTy (μ A B) (A' ⇒ B') = false
decRTy (μ A B) (Π K' A') = false
decRTy (μ A B) (ƛ K' A') = false
decRTy (μ A B) (A' · A'') = false
decRTy (μ A B) (con c') = false
decRTy (μ A B) (μ A' B') with decRTy A A'
... | false = false
... | true with decRTy B B'
... | false = false
... | true = true

decRTm : (t t' : RawTm) → Bool
decRTm (` x) (` x') with x ≟ x'
decRTm (` x) (` x') | yes _ = true
decRTm (` x) (` x') | no  _ = false
decRTm (Λ K t) (Λ K' t') with decRKi K K'
... | false = false
... | true with decRTm t t'
... | true = true
... | false = false
decRTm (t ·⋆ A) (t' ·⋆ A') with decRTm t t'
... | false = false
... | true with decRTy A A'
... | true = true
... | false = false
decRTm (ƛ A t) (ƛ A' t') with decRTy A A'
... | false = false
... | true with decRTm t t'
... | false = false
... | true = true
decRTm (t · u) (t' · u') with decRTm t t'
... | false = false
... | true with decRTm u u'
... | false = false
... | true = true
decRTm (con c) (con c') = decTagCon c c'
decRTm (error A) (error A') with decRTy A A'
... | true = true
... | false = false
decRTm (builtin b) (builtin b') = decBuiltin b b'
decRTm (wrap pat arg t) (wrap pat' arg' t') with decRTy pat pat'
... | false = false
... | true with decRTy arg arg'
... | false = false
... | true with decRTm t t'
... | false = false
... | true = true
decRTm (unwrap t) (unwrap t') with decRTm t t'
decRTm (unwrap t) (unwrap t') | true = true
decRTm (unwrap t) (unwrap t') | false = false
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
rawPrinter (wrap pat arg t) = "(wrap" ++ ")"
rawPrinter (unwrap t) = "(unwrap" ++ rawPrinter t ++ ")"
\end{code}
 