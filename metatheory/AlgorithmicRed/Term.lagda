\begin{code}
module AlgorithmicRed.Term where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)



open import Type
open import Type.RenamingSubstitution
open import Type.BetaNormal

open import Type.BetaNBE
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Data.Unit
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
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Ctx
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
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢Nf⋆ J}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢Nf⋆ J} {B : ∥ Γ ∥ ⊢Nf⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢Nf⋆ J}
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


open import Type.Reduction
_—Nf→⋆_ : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K → Set
A —Nf→⋆ N = Σ (_ ⊢⋆ _) λ A' → (A —→⋆ A') × Value⋆ A' × embNf N ≡ A'

-- value predicate and normal forms coincide

val2nf : ∀{Γ K}{A : Γ ⊢⋆ K} → Value⋆ A → Σ (Γ ⊢Nf⋆ K) λ N → embNf N ≡ A
neu2nen : ∀{Γ K}{A : Γ ⊢⋆ K} → Neutral⋆ A → Σ (Γ ⊢NeN⋆ K) λ N → embNeN N ≡ A

val2nf (V-Π VN) with val2nf VN
... | N ,, q = Π _ N ,, cong (Π _) q
val2nf (VM V-⇒ VN) with val2nf VM | val2nf VN
... | M ,, p | N ,, q = M ⇒ N ,, cong₂ _⇒_ p q
val2nf (V-ƛ VN) with val2nf VN
... | N ,, p = ƛ _ N ,, cong (ƛ _) p
val2nf (N- VN) with neu2nen VN
... | N ,, p = ne N ,, p
val2nf (V-con {tcn = tcn})= con tcn ,, refl

neu2nen N-μ1 = _ ,, refl
neu2nen (N-· NA VB) with neu2nen NA | val2nf VB
... | A ,, p | B ,, q = A · B ,, cong₂ _·_ p q
neu2nen N-` = _ ,, refl
infix 4 _—Nf→⋆_

Tel : ∀ Γ Δ → (∀ {J} → Δ ∋⋆ J → ∥ Γ ∥ ⊢Nf⋆ J) → List (Δ ⊢Nf⋆ *) → Set

data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Set where

  ` : ∀ {Γ J} {A : ∥ Γ ∥ ⊢Nf⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Γ A B A'}
    → A —Nf→⋆ A'
    → Γ , A' ⊢ B
      -----------
    → Γ ⊢ A' ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Γ K}{x}
    → {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π x B

  _·⋆_ : ∀ {Γ K}{x}
    → {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π x B
    → (A : ∥ Γ ∥ ⊢Nf⋆ K)
    → {R : ∥ Γ ∥ ⊢Nf⋆ *}
    → embNf B [ embNf A ] —Nf→⋆ R
      ---------------
    → Γ ⊢ R

  wrap1 : ∀{Γ K}
   → (pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : ∥ Γ ∥ ⊢Nf⋆ K)
   → {R : ∥ Γ ∥ ⊢Nf⋆ *}
   → embNf pat · (μ1 · embNf pat) · embNf arg —Nf→⋆ R
   → (term : Γ ⊢ R)
   → Γ ⊢ ne (μ1 · pat · arg)

  unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → (term : Γ ⊢ ne (μ1 · pat · arg))
    → {R : ∥ Γ ∥ ⊢Nf⋆ *}
    → embNf pat · (μ1 · embNf pat) · embNf arg —Nf→⋆ R
    → Γ ⊢ R

  con : ∀{Γ tcn}
    → TermCon {Φ = ∥ Γ ∥} (con tcn )
      -------------------
    → Γ ⊢ con tcn

  builtin : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {J} → Δ ∋⋆ J → ∥ Γ ∥ ⊢Nf⋆ J)
    → Tel Γ Δ σ As
    → {R : ∥ Γ ∥ ⊢Nf⋆ *}
    → subst (embNf ∘ σ) (embNf C) —Nf→⋆ R
      ----------------------------------
    → Γ ⊢ R

  error : ∀{Γ} → (A : ∥ Γ ∥ ⊢⋆ *){R : ∥ Γ ∥ ⊢Nf⋆ *} → A —Nf→⋆ R → Γ ⊢ R

Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = 
  Σ (∥ Γ ∥ ⊢Nf⋆ *) λ N →
    subst (embNf ∘ σ) (embNf A) —Nf→⋆ N
  × Γ ⊢ N
  × Tel Γ Δ σ As
\end{code}

# Term Abbreviations
\begin{code}
--void : ∀{Γ} → Γ ⊢ unitNf
--void = Λ (ƛ (` Z))
{-
true : ∀{Γ} → Γ ⊢ booleanNf
true = Λ (ƛ (ƛ (` (S Z))))

false : ∀{Γ} → Γ ⊢ booleanNf
false = Λ (ƛ (ƛ (` Z)))
-}
\end{code}
