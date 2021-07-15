\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ;_≟_)
open import Data.Integer using (ℤ)
open import Data.Integer.Show
open import Data.Char using (Char)
open import Data.Unit using (⊤)

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
  integer    : ℤ → RawTermCon
  bytestring : ByteString → RawTermCon
  string     : String → RawTermCon
  bool       : Bool → RawTermCon
  char       : Char → RawTermCon
  unit       : RawTermCon

data RawTm : Set where
  `             : ℕ → RawTm
  Λ             : RawKind → RawTm → RawTm
  _·⋆_          : RawTm → RawTy → RawTm
  ƛ             : RawTy → RawTm → RawTm
  _·_           : RawTm → RawTm → RawTm
  con           : RawTermCon → RawTm
  error         : RawTy → RawTm
  builtin       : Builtin → RawTm
  wrap          : RawTy → RawTy → RawTm → RawTm
  unwrap        : RawTm → RawTm

-- α equivalence

-- we don't have a decicable equality instance for bytestring, so I
-- converted this to bool for now

decRTyCon : (C C' : TyCon) → Bool
decRTyCon integer integer = true
decRTyCon bytestring bytestring = true
decRTyCon string     string     = true
decRTyCon char       char       = true
decRTyCon unit       unit       = true
decRTyCon bool       bool       = true
decRTyCon _          _          = false


decTermCon : (C C' : RawTermCon) → Bool
decTermCon (integer i) (integer i') with i Data.Integer.≟ i'
... | yes p = true
... | no ¬p = false
decTermCon (bytestring b) (bytestring b') with equals b b'
decTermCon (bytestring b) (bytestring b') | false = false
decTermCon (bytestring b) (bytestring b') | true = true
decTermCon (string s) (string s') with s Data.String.≟ s'
... | yes p = true
... | no ¬p = false
decTermCon (bool b) (bool b') with b Data.Bool.≟ b'
... | yes p = true
... | no ¬p = false
decTermCon unit unit = true
-- TODO: char?
decTermCon _ _ = false

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
decBuiltin chatToString charToString = true
decBuiltin append append = true
decBuiltin trace trace = true
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
decRTm (con c) (con c') = decTermCon c c'
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
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC RawTermCon = data RConstant (RConInt | RConBS | RConStr | RConBool | RConChar | RConUnit) #-}
{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap) #-}
{-# COMPILE GHC RawTy = data RType (RTyVar | RTyFun | RTyPi | RTyLambda | RTyApp | RTyCon | RTyMu) #-}
{-# COMPILE GHC RawKind = data RKind (RKiStar | RKiFun) #-}

-- We have to different approaches to de Bruijn terms.
-- one counts type and term binders separately the other counts them together

rawTyPrinter : RawTy → String
rawTyPrinter (` x)   = Data.Integer.Show.show (ℤ.pos x)
rawTyPrinter (A ⇒ B) = "(" ++ rawTyPrinter A ++ "⇒" ++ rawTyPrinter B ++ ")"
rawTyPrinter (Π K A) = "(Π" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (ƛ K A) = "(ƛ" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (A · B) = "(" ++ rawTyPrinter A ++ "·" ++ rawTyPrinter B ++ ")"
rawTyPrinter (con c) = "(con)"
rawTyPrinter (μ A B) = "(μ" ++ rawTyPrinter A ++ rawTyPrinter B ++ ")"

rawPrinter : RawTm → String
rawPrinter (` x) = Data.Integer.Show.show (ℤ.pos x)
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
