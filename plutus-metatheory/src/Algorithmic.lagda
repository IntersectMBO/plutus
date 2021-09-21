\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
open import Data.Sum

open import Utils hiding (TermCon)
open import Type
open import Type.BetaNormal
import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *)
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  4 _⊢_
infixl 5 _,_
\end{code}

## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
--data Ctx : Set
--∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx : Ctx⋆ → Set where
  ∅    : Ctx ∅
  _,⋆_ : ∀{Φ} → Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_  : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Ctx Φ
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
--∥ ∅ ∥       =  ∅
--∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
--∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
open import Type.BetaNormal.Equality
data _∋_ : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  Z : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weakenNf A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
ISIG : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢Nf⋆ *
ISIG ifThenElse = _ ,, ∅ ,⋆ * , con bool , ne (` Z) , ne (` Z) ,, ne (` Z)
ISIG addInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG subtractInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG multiplyInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG divideInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG quotientInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG remainderInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG modInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
ISIG lessThanInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG lessThanEqualsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG equalsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
ISIG appendByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bytestring
ISIG lessThanByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool
ISIG lessThanEqualsByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool
ISIG sha2-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
ISIG sha3-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
ISIG verifySignature = ∅ ,, ∅ , con bytestring , con bytestring , con bytestring ,, con bool
ISIG equalsByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool
ISIG appendString = ∅ ,, ∅ , con string , con string ,, con string
ISIG trace = _ ,, ∅ ,⋆ * , con string , ne (` Z) ,, ne (` Z)
ISIG equalsString = ∅ ,, ∅ , con string , con string ,, con bool
ISIG encodeUtf8 = ∅ ,, ∅ , con string ,, con bytestring
ISIG decodeUtf8 = ∅ ,, ∅ , con bytestring ,, con string
ISIG fstPair =
  _ ,, ∅ ,⋆ * ,⋆ * , con (pair (ne (` (S Z))) (ne (` Z))) ,, ne (` (S Z))
ISIG sndPair = 
  _ ,, ∅ ,⋆ * ,⋆ * , con (pair (ne (` (S Z))) (ne (` Z))) ,, ne (` Z)
ISIG nullList = _ ,, ∅ ,⋆ * , con (list (ne (` Z))) ,, con bool
ISIG headList = _ ,, ∅ ,⋆ * , con (list (ne (` Z))) ,, ne (` Z)
ISIG tailList = _ ,, ∅ ,⋆ * , con (list (ne (` Z))) ,, con (list (ne (` Z)))
ISIG chooseList =
  _
  ,,
  ∅ ,⋆ * ,⋆ * , ne (` (S Z)) , ne (` (S Z)) , con (list (ne (` Z)))
  ,,
  ne (` (S Z)) 
ISIG constrData = _ ,, ∅ , con integer , con (list (con Data)) ,, con Data
ISIG mapData = _ ,, ∅ , con (pair (con Data) (con Data)) ,, con Data
ISIG listData = _ ,, ∅ , con (list (con Data)) ,, con Data
ISIG iData = _ ,, ∅ , con integer ,, con Data
ISIG bData = _ ,, ∅ , con bytestring ,, con Data
ISIG unConstrData =
  _ ,, ∅ , con Data ,, con (pair (con integer) (con (list (con Data))))
ISIG unMapData = _ ,, ∅ , con Data ,, con (pair (con Data) (con Data))
ISIG unListData = _ ,, ∅ , con Data ,, con (list (con Data))
ISIG unIData = _ ,, ∅ , con Data ,, con integer
ISIG unBData = _ ,, ∅ , con Data ,, con bytestring
ISIG equalsData = _ ,, ∅ , con Data , con Data ,, con bool
ISIG chooseData =
  _
  ,,
  ∅ ,⋆ * , ne (` Z) , ne (` Z) , ne (` Z) , ne (` Z) , ne (` Z) , con Data
  ,,
  ne (` Z)
ISIG chooseUnit = _ ,, ∅ ,⋆ * , ne (` Z) , con unit ,, ne (` Z)
ISIG mkPairData =
  _ ,, ∅ , con Data , con Data ,, con (pair (con Data) (con Data)) 
ISIG mkNilData = _ ,, ∅ , con unit ,, con (list (con Data))
ISIG mkNilPairData = _ ,, ∅ , con unit ,, con (list (con (pair (con Data) (con Data))))
ISIG mkCons =
  _ ,, ∅ , con Data , con (list (con Data)) ,, con (list (con Data))
ISIG consByteString = _ ,, ∅ , con integer , con bytestring ,, con bytestring
ISIG sliceByteString =
  _ ,, ∅ , con integer , con integer , con bytestring ,, con bytestring
ISIG lengthOfByteString = _ ,, ∅ , con bytestring ,, con integer
ISIG indexByteString = _ ,, ∅ , con bytestring , con integer ,, con integer
ISIG blake2b-256 = _ ,, ∅ , con bytestring ,, con bytestring

isig2type : (Φ : Ctx⋆) → Ctx Φ → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
isig2type .∅ ∅ C = C
isig2type (Φ ,⋆ J) (Γ ,⋆ J) C = isig2type Φ Γ (Π C)
isig2type Φ        (Γ ,  A) C = isig2type Φ Γ (A ⇒ C)

itype : ∀{Φ} → Builtin → Φ ⊢Nf⋆ *
itype b = let Φ ,, Γ ,, C = ISIG b in subNf (λ()) (isig2type Φ Γ C)

postulate itype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → itype b ≡ renNf ρ (itype b)
postulate itype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → itype b ≡ subNf ρ (itype b)

infixl 7 _·⋆_

data _⊢_ {Φ} (Γ : Ctx Φ) : Φ ⊢Nf⋆ * → Set where

  ` : ∀ {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : Φ ⊢Nf⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{K}
   → (A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢Nf⋆ K)
   → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
   → Γ ⊢ μ A B

  unwrap : ∀{K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → Γ ⊢ μ A B
    → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)

  con : ∀{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  ibuiltin : (b :  Builtin) → Γ ⊢ itype b

  error : (A : Φ ⊢Nf⋆ *) → Γ ⊢ A
\end{code}

Utility functions

\begin{code}
open import Type.BetaNormal.Equality

conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ∋ A
 → Γ' ∋ A'
conv∋ refl refl x = x

open import Type.BetaNBE.Completeness
open import Type.Equality
open import Type.BetaNBE.RenamingSubstitution

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

Ctx2type : ∀{Φ}(Γ : Ctx Φ) → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
Ctx2type ∅        C = C
Ctx2type (Γ ,⋆ J) C = Ctx2type Γ (Π C)
Ctx2type (Γ , x)  C = Ctx2type Γ (x ⇒ C)

data Arg : Set where
  Term Type : Arg

Arity = List Arg

ctx2bwdarity : ∀{Φ}(Γ : Ctx Φ) → Bwd Arg
ctx2bwdarity ∅        = []
ctx2bwdarity (Γ ,⋆ J) = ctx2bwdarity Γ :< Type
ctx2bwdarity (Γ , A)  = ctx2bwdarity Γ :< Term

arity : Builtin → Arity
arity b = ctx2bwdarity (proj₁ (proj₂ (ISIG b))) <>> []
\end{code}
