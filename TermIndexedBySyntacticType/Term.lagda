\begin{code}
module TermIndexedBySyntacticType.Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Agda.Builtin.Int
open import Data.Integer renaming (_*_ to _**_)
open import Data.Empty
open import Data.Product hiding (_,_)
open import Relation.Binary hiding (_⇒_)
import Data.Nat as ℕ
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_
\end{code}

## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
data Ctx : Set
∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx where
  ∅ : Ctx
  _,⋆_ : Ctx → Kind → Ctx
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Ctx
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
∥ ∅ ∥       =  ∅
∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken A
\end{code}
Let `x`, `y` range over variables.

## Term Constants


\begin{code}
postulate
  ByteString : Set
  length : ByteString → ℕ.ℕ

  div  : Int → Int → Int
  quot : Int → Int → Int
  rem  : Int → Int → Int
  mod  : Int → Int → Int

  append : ByteString → ByteString → ByteString
  take   : Int → ByteString → ByteString
  drop   : Int → ByteString → ByteString

{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC length = type BS.length #-}

{-# COMPILE GHC div  = type div  #-}
{-# COMPILE GHC quot = type quot #-}
{-# COMPILE GHC rem  = type rem  #-}
{-# COMPILE GHC mod  = type mod  #-}

{-# COMPILE GHC append = BS.append #-}
{-# COMPILE GHC take = BS.take #-}
{-# COMPILE GHC drop = BS.drop #-}


-- cut-off exponentiation
_^_ : Int → Int → Int
x ^ negsuc n      = pos 1
x ^ pos ℕ.zero    = pos 1
x ^ pos (ℕ.suc n) = x ** (x ^ pos n)

BoundedI : ∀ s i → Set
BoundedI s i = (negsuc 1 ^ (pos 8 ** (s ⊖ 1))) ≤ i × i < (pos 2 ^ (pos 8 ** (s ⊖ 1)))

BoundedB : ∀ s b → Set
BoundedB s b = length b ℕ.< s

-- TODO
postulate
  boundedI? : Decidable BoundedI
  boundedB? : Decidable BoundedB
  
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    : ∀ s
    → (i : Int)
    → BoundedI s i
    → TermCon (con integer (size⋆ s))
  bytestring : ∀ s
    → (b : ByteString)
    → BoundedB s b
    → TermCon (con bytestring (size⋆ s))
  size       : ∀ s → TermCon (con size (size⋆ s)) 
\end{code}

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
open import Data.Vec hiding ([_])
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Function hiding (_∋_)

Sig : Ctx → Ctx → Set
Sig Δ Γ = List (∥ Δ ∥ ⊢⋆ *) × ∥ Δ ∥ ⊢⋆ *

data Builtin : Set where
  addInteger       : Builtin
  subtractInteger : Builtin
  multiplyInteger          : Builtin
  divideInteger            : Builtin
  quotientInteger          : Builtin
  remainderInteger         : Builtin
  modInteger               : Builtin
  -- lessThanInteger          : Builtin
  -- lessThanEqualsInteger    : Builtin
  -- greaterThanInteger       : Builtin
  -- greaterThanEqualsInteger : Builtin
  -- equalsInteger            : Builtin
  -- resizeInteger            : Builtin
  -- sizeOfInteger            : Builtin
  -- intToByteString          : Builtin

  concatenate      : Builtin
  takeByteString   : Builtin
  dropByteString   : Builtin
  -- sha2_256         : Builtin
  -- sha3_256         : Builtin
  -- verifySignature  : Builtin
  -- resizeByteString : Builtin
  -- equalsByteString : Builtin
  -- txhash           : Builtin
  -- blocknum         : Builtin
  
SIG : Builtin → ∀ Γ → Σ Ctx λ Δ → Sig Δ Γ
-- could have just one context so Signatures extend from ∅...
-- going in the other direction could take a substitution as an arg and
-- extend it appropriately...
SIG addInteger       Γ =
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG subtractInteger Γ = 
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG multiplyInteger Γ = 
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
SIG concatenate      Γ =
  Γ ,⋆ #
  ,,
  con bytestring (` Z) ∷ con bytestring (` Z) ∷ []
  ,,
  con bytestring (` Z)
SIG takeByteString Γ =
  (Γ ,⋆ #  ,⋆ #)
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG dropByteString Γ =
  (Γ ,⋆ #  ,⋆ #)
  ,,
  (con integer (` (S Z)) ∷ con bytestring (` Z) ∷ [])
  ,,
  con bytestring (` Z)
SIG divideInteger    Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG quotientInteger  Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG remainderInteger Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)
SIG modInteger       Γ =
  (Γ ,⋆ #)
  ,,
  con integer (` Z) ∷ con integer (` Z) ∷ []
  ,,
  con integer (` Z)

Tel : ∀ Γ Δ → Sub ∥ Δ ∥ ∥ Γ ∥ → List (∥ Δ ∥ ⊢⋆ *) → Set

data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  ` : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Γ A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Γ B}
    → Γ ⊢ Π B
    → (A : ∥ Γ ∥ ⊢⋆ *)
      ---------------
    → Γ ⊢ B [ A ]

  wrap1 : ∀{Γ K}
   → (pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : ∥ Γ ∥ ⊢⋆ K)
   → (term : Γ ⊢ pat · (μ1 · pat) · arg)
   → Γ ⊢ μ1 · pat · arg

  unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → (term : Γ ⊢ μ1 · pat · arg)
    → Γ ⊢ pat · (μ1 · pat) · arg
    
  conv : ∀{Γ J}
    → {A B : ∥ Γ ∥ ⊢⋆ J}
    → A ≡β B
    → Γ ⊢ A
      -----
    → Γ ⊢ B

  con : ∀{Γ s tcn}
    → TermCon (con tcn s)
      -------------------
    → Γ ⊢ con tcn s

  builtin : ∀{Γ'}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn ∅ in
      (σ : Sub ∥ Δ ∥ ∥ ∅ ∥)   -- substitutes for new vars introduced by the Sig
    → Tel ∅ Δ σ As           -- a telescope of terms M_i typed in subst σ A_i
    → (σ' : Sub ∥ ∅ ∥ ∥ Γ' ∥) -- a delayed substitution applied after computation
      -----------------------------
    → Γ' ⊢ subst σ' (subst σ C)

  error : ∀{Γ} → (A : ∥ Γ ∥ ⊢⋆ *) → Γ ⊢ A

open import Data.Unit
Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ subst σ A × Tel Γ Δ σ As

\end{code}
