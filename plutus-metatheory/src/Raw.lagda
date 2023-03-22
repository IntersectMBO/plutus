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

open import Builtin using (Builtin;equals)
open Builtin.Builtin

open import Utils using (Kind;*;_⇒_;TermCon)
open TermCon
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
  integer              : RawTyCon
  bytestring           : RawTyCon
  string               : RawTyCon
  unit                 : RawTyCon
  bool                 : RawTyCon
  list                 : RawTy → RawTyCon
  pair                 : RawTy → RawTy → RawTyCon
  pdata                : RawTyCon
  bls12-381-g1-element : RawTyCon
  bls12-381-g2-element : RawTyCon
  bls12-381-mlresult   : RawTyCon


{-# COMPILE GHC RawTyCon = data RTyCon (RTyConInt | RTyConBS | RTyConStr | RTyConUnit | RTyConBool | RTyConList | RTyConPair | RTyConData | RTyConG1elt | RTyConG2elt | RTyConMlResult) #-}

data RawTm : Set where
  `             : ℕ → RawTm
  Λ             : Kind → RawTm → RawTm
  _·⋆_          : RawTm → RawTy → RawTm
  ƛ             : RawTy → RawTm → RawTm
  _·_           : RawTm → RawTm → RawTm
  con           : TermCon → RawTm
  error         : RawTy → RawTm
  builtin       : Builtin → RawTm
  wrap          : RawTy → RawTy → RawTm → RawTm
  unwrap        : RawTm → RawTm

{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap) #-}

-- α equivalence

-- we don't have a decicable equality instance for bytestring, so I
-- converted this to bool for now

decRTyCon : (C C' : RawTyCon) → Bool
decRTyCon integer    integer    = true
decRTyCon bytestring bytestring = true
decRTyCon string     string     = true
decRTyCon unit       unit       = true
decRTyCon bool       bool       = true
decRTyCon bls12-381-g1-element bls12-381-g1-element = true
decRTyCon bls12-381-g2-element bls12-381-g2-element = true
decRTyCon bls12-381-mlresult   bls12-381-mlresult   = true  -- Maybe not: no eq for bls12-381-mlresult in Plutus
decRTyCon _          _          = false

decTermCon : (C C' : TermCon) → Bool
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
-- FIXME: not sure what to do about the BLS types here.
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
decBuiltin equalsInteger equalsInteger = true
decBuiltin appendByteString appendByteString = true
decBuiltin sha2-256 sha2-256 = true
decBuiltin sha3-256 sha3-256 = true
decBuiltin verifyEd25519Signature verifyEd25519Signature = true
decBuiltin verifyEcdsaSecp256k1Signature verifyEcdsaSecp256k1Signature = true
decBuiltin verifySchnorrSecp256k1Signature verifySchnorrSecp256k1Signature = true
decBuiltin equalsByteString equalsByteString = true
decBuiltin appendString appendString = true
decBuiltin trace trace = true
decBuiltin bls12-381-G1-add bls12-381-G1-add = true
decBuiltin bls12-381-G1-neg bls12-381-G1-neg = true
decBuiltin bls12-381-G1-scalarMul bls12-381-G1-scalarMul = true
decBuiltin bls12-381-G1-equal bls12-381-G1-equal = true
decBuiltin bls12-381-G1-hashToGroup bls12-381-G1-hashToGroup = true
decBuiltin bls12-381-G1-compress bls12-381-G1-compress = true
decBuiltin bls12-381-G1-uncompress bls12-381-G1-uncompress = true
decBuiltin bls12-381-G2-add bls12-381-G2-add = true
decBuiltin bls12-381-G2-neg bls12-381-G2-neg = true
decBuiltin bls12-381-G2-scalarMul bls12-381-G2-scalarMul = true
decBuiltin bls12-381-G2-equal bls12-381-G2-equal = true
decBuiltin bls12-381-G2-hashToGroup bls12-381-G2-hashToGroup = true
decBuiltin bls12-381-G2-compress bls12-381-G2-compress = true
decBuiltin bls12-381-G2-uncompress bls12-381-G2-uncompress = true
decBuiltin bls12-381-millerLoop bls12-381-millerLoop = true
decBuiltin bls12-381-mulMlResult bls12-381-mulMlResult = true
decBuiltin bls12-381-finalVerify bls12-381-finalVerify = true
decBuiltin _ _ = false

decRKi : (K K' : Kind) → Bool
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
