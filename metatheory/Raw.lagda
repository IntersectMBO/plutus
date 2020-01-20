\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ;_≟_)
open import Data.Integer using (ℤ)

open import Builtin.Constant.Type
open import Builtin

open import Relation.Nullary using (Reflects;Dec;ofʸ;ofⁿ;_because_;yes;no)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_;cong;cong₂;refl)
open import Data.Bool using (Bool;false;true)
\end{code}

The raw un-scope-checked and un-type-checked syntax

\begin{code}

data RawKind : Set where
  *   : RawKind
  _⇒_ : RawKind → RawKind → RawKind

data RawTy : Set where
  `   : ℕ → RawTy
  _⇒_ : RawTy → RawTy → RawTy
  Π   : RawKind → RawTy → RawTy
  ƛ   : RawKind → RawTy → RawTy
  _·_ : RawTy → RawTy → RawTy
  con : TyCon → RawTy
  μ    : RawTy → RawTy → RawTy

data RawTermCon : Set where
  integer : ℤ → RawTermCon
  bytestring : ByteString → RawTermCon
  string : String → RawTermCon

data RawTm : Set where
  `       : ℕ → RawTm
  Λ       : RawKind → RawTm → RawTm
  _·⋆_    : RawTm → RawTy → RawTm
  ƛ       : RawTy → RawTm → RawTm
  _·_     : RawTm → RawTm → RawTm
  con     : RawTermCon → RawTm
  error   : RawTy → RawTm
  builtin : Builtin → RawTm
  wrap    : RawTy → RawTy → RawTm → RawTm
  unwrap  : RawTm → RawTm

-- α equivalence

-- we don't have a decicable equality instance for bytestring, so I
-- converted this to bool for now

decRTyCon : (C C' : TyCon) → Bool
decRTyCon integer integer = true
decRTyCon integer bytestring = false
decRTyCon integer string = false
decRTyCon bytestring integer = false
decRTyCon bytestring bytestring = true
decRTyCon bytestring string = false
decRTyCon string integer = false
decRTyCon string bytestring = false
decRTyCon string string = true

decTermCon : (C C' : RawTermCon) → Bool
decTermCon (integer i) (integer i') with i Data.Integer.≟ i'
... | yes p = true
... | no ¬p = false
decTermCon (integer i) (bytestring b') = false
decTermCon (integer i) (string s') = false
decTermCon (bytestring b) (integer i') = false
decTermCon (bytestring b) (bytestring b') with equals b b'
decTermCon (bytestring b) (bytestring b') | false = false
decTermCon (bytestring b) (bytestring b') | true = true
decTermCon (bytestring b) (string s') = false
decTermCon (string s) (integer i') = false
decTermCon (string s) (bytestring b') = false
decTermCon (string s) (string s') with s Data.String.≟ s'
... | yes p = true
... | no ¬p = false

decBuiltin : (b b' : Builtin) → Bool
decBuiltin addInteger addInteger = true
decBuiltin subtractInteger subtractInteger = true
decBuiltin multiplyInteger multiplyInteger = true
decBuiltin divideInteger divideInteger = true
decBuiltin quotientInteger quotientInteger = true
decBuiltin remainderInteger remainderInteger = true
decBuiltin modInteger modInteger = true
decBuiltin lessThanInteger lessThanInteger = true
decBuiltin lessThanEqualsInteger lessThanEqualsInteger = true
decBuiltin greaterThanInteger greaterThanInteger = true
decBuiltin greaterThanEqualsInteger greaterThanEqualsInteger = true
decBuiltin equalsInteger equalsInteger = true
decBuiltin concatenate concatenate = true
decBuiltin takeByteString takeByteString = true
decBuiltin dropByteString dropByteString = true
decBuiltin sha2-256 sha2-256 = true
decBuiltin sha3-256 sha3-256 = true
decBuiltin verifySignature verifySignature = true
decBuiltin equalsByteString equalsByteString = true
decBuiltin _ _ = false

decRKi : (K K' : RawKind) → Bool
decRKi * * = true
decRKi * (K' ⇒ J') = false
decRKi (K ⇒ J) * = false
decRKi (K ⇒ J) (K' ⇒ J') with decRKi K K'
decRKi (K ⇒ J) (K' ⇒ J') | true with decRKi J J'
decRKi (K ⇒ J) (K' ⇒ J') | true | true = true
decRKi (K ⇒ J) (K' ⇒ J') | true | false = false 
decRKi (K ⇒ J) (K' ⇒ J') | false = false

decRTy : (A A' : RawTy) → Bool
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
decRTm (` x) (Λ K t')  = false
decRTm (` x) (t' ·⋆ A') = false
decRTm (` x) (ƛ A' t') = false
decRTm (` x) (t' · u') = false
decRTm (` x) (con c') = false
decRTm (` x) (error A') = false
decRTm (` x) (builtin b') = false
decRTm (` x) (wrap pat' arg' t') = false
decRTm (` x) (unwrap t') = false
decRTm (Λ K t) (` x') = false
decRTm (Λ K t) (Λ K' t') with decRKi K K'
... | false = false
... | true with decRTm t t'
... | true = true
... | false = false
decRTm (Λ K t) (t' ·⋆ A') = false
decRTm (Λ K t) (ƛ A' t') = false
decRTm (Λ K t) (t' · t'') = false
decRTm (Λ K t) (con c') = false
decRTm (Λ K t) (error A') = false
decRTm (Λ K t) (builtin b') = false
decRTm (Λ K t) (wrap pat' arg' t') = false
decRTm (Λ K t) (unwrap t') = false
decRTm (t ·⋆ A) (` x') = false
decRTm (t ·⋆ A) (Λ K t') = false
decRTm (t ·⋆ A) (t' ·⋆ A') with decRTm t t'
... | false = false
... | true with decRTy A A'
... | true = true
... | false = false
decRTm (t ·⋆ A) (ƛ A' t') = false
decRTm (t ·⋆ A) (t' · u') = false
decRTm (t ·⋆ A) (con c') = false
decRTm (t ·⋆ A) (error A') = false
decRTm (t ·⋆ A) (builtin b') = false
decRTm (t ·⋆ A) (wrap pat' arg' t') = false
decRTm (t ·⋆ A) (unwrap t') = false
decRTm (ƛ A t) (` x') = false
decRTm (ƛ A t) (Λ K t') = false
decRTm (ƛ A t) (t' ·⋆ A') = false
decRTm (ƛ A t) (ƛ A' t') with decRTy A A'
... | false = false
... | true with decRTm t t'
... | false = false
... | true = true
decRTm (ƛ A t) (t' · u') = false
decRTm (ƛ A t) (con c') = false
decRTm (ƛ A t) (error A') = false
decRTm (ƛ A t) (builtin b') = false
decRTm (ƛ A t) (wrap pat' arg' t') = false
decRTm (ƛ A t) (unwrap t') = false
decRTm (t · u) (` x) = false
decRTm (t · u) (Λ K t') = false
decRTm (t · u) (t' ·⋆ A') = false
decRTm (t · u) (ƛ A' t') = false
decRTm (t · u) (t' · u') with decRTm t t'
... | false = false
... | true with decRTm u u'
... | false = false
... | true = true
decRTm (t · u) (con c') = false
decRTm (t · u) (error A') = false
decRTm (t · u) (builtin b') = false
decRTm (t · u) (wrap pat' arg' t') = false
decRTm (t · u) (unwrap t') = false
decRTm (con c) (` x') = false
decRTm (con c) (Λ K' t') = false
decRTm (con c) (t' ·⋆ A') = false
decRTm (con c) (ƛ A' t') = false
decRTm (con c) (t' · u') = false
decRTm (con c) (con c') = decTermCon c c'
decRTm (con c) (error A') = false
decRTm (con c) (builtin b') = false
decRTm (con c) (wrap pat' arg' t') = false
decRTm (con c) (unwrap t') = false
decRTm (error A) (` x') = false
decRTm (error A) (Λ K' t') = false
decRTm (error A) (t' ·⋆ A') = false
decRTm (error A) (ƛ A' t') = false
decRTm (error A) (t' · u') = false
decRTm (error A) (con c') = false
decRTm (error A) (error A') with decRTy A A'
... | true = true
... | false = false
decRTm (error A) (builtin b') = false
decRTm (error A) (wrap pat' arg' t') = false
decRTm (error A) (unwrap t') = false
decRTm (builtin b) (` x') = false
decRTm (builtin b) (Λ K t') = false
decRTm (builtin b) (t' ·⋆ A') = false
decRTm (builtin b) (ƛ A' t') = false
decRTm (builtin b) (t' · u') = false
decRTm (builtin b) (con c') = false
decRTm (builtin b) (error A') = false
decRTm (builtin b) (builtin b') = decBuiltin b b'
decRTm (builtin b) (wrap pat' arg' t') = false
decRTm (builtin b) (unwrap t') = false
decRTm (wrap pat arg t) (` x') = false
decRTm (wrap pat arg t) (Λ K' t') = false
decRTm (wrap pat arg t) (t' ·⋆ A') = false
decRTm (wrap pat arg t) (ƛ A' t') = false
decRTm (wrap pat arg t) (t' · u') = false
decRTm (wrap pat arg t) (con c') = false
decRTm (wrap pat arg t) (error A') = false
decRTm (wrap pat arg t) (builtin b') = false
decRTm (wrap pat arg t) (wrap pat' arg' t') with decRTy pat pat'
... | false = false
... | true with decRTy arg arg'
... | false = false
... | true with decRTm t t'
... | false = false
... | true = true 
decRTm (wrap pat arg t) (unwrap t') = false
decRTm (unwrap t) (` x') = false
decRTm (unwrap t) (Λ K' t') = false
decRTm (unwrap t) (t' ·⋆ A') = false
decRTm (unwrap t) (ƛ A' t') = false
decRTm (unwrap t) (t' · u') = false
decRTm (unwrap t) (con c') = false
decRTm (unwrap t) (error A') = false
decRTm (unwrap t) (builtin b') = false
decRTm (unwrap t) (wrap pat' arg' t') = false
decRTm (unwrap t) (unwrap t') with decRTm t t'
decRTm (unwrap t) (unwrap t') | true = true
decRTm (unwrap t) (unwrap t') | false = false

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC RawTermCon = data RConstant (RConInt | RConBS | RConStr) #-}
{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap) #-}
{-# COMPILE GHC RawTy = data RType (RTyVar | RTyFun | RTyPi | RTyLambda | RTyApp | RTyCon | RTyMu) #-}
{-# COMPILE GHC RawKind = data RKind (RKiStar | RKiFun) #-}

-- We have to different approaches to de Bruijn terms.
-- one counts type and term binders separately the other counts them together

rawTyPrinter : RawTy → String
rawTyPrinter (` x)   = Data.Integer.show (ℤ.pos x)
rawTyPrinter (A ⇒ B) = "(" ++ rawTyPrinter A ++ "⇒" ++ rawTyPrinter B ++ ")"
rawTyPrinter (Π K A) = "(Π" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (ƛ K A) = "(ƛ" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (A · B) = "(" ++ rawTyPrinter A ++ "·" ++ rawTyPrinter B ++ ")"
rawTyPrinter (con c) = "(con)"
rawTyPrinter (μ A B) = "(μ" ++ rawTyPrinter A ++ rawTyPrinter B ++ ")"

rawPrinter : RawTm → String
rawPrinter (` x) = Data.Integer.show (ℤ.pos x)
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
