\begin{code}
module Type.Normal where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _⊢Nf⋆_
\end{code}

## Imports

\begin{code}
open import Type
open import Type.Value
\end{code}

## Type β-normal forms

\begin{code}

data _⊢Nf⋆_ : Ctx⋆ → Kind → Set

data _⊢NeN⋆_ : Ctx⋆ → Kind → Set where
  `_ : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢NeN⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢NeN⋆ (K ⇒ J)
    → Φ ⊢Nf⋆ K
      ------
    → Φ ⊢NeN⋆ J


data _⊢Nf⋆_ where

  Π : ∀ {Φ K}
    → Φ ,⋆ K ⊢Nf⋆ *
      -----------
    → Φ ⊢Nf⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢Nf⋆ *
    → Φ ⊢Nf⋆ *
      ------
    → Φ ⊢Nf⋆ *

  ƛ :  ∀ {Φ K J}
    → Φ ,⋆ K ⊢Nf⋆ J
      -----------
    → Φ ⊢Nf⋆ (K ⇒ J)

  μ : ∀{φ K}
    → φ ,⋆ K ⊢Nf⋆ *
      -----------
    → φ ⊢Nf⋆ *

  ne : ∀{φ K} -- if it was at kind * it would be βη-normal forms
    → φ ⊢NeN⋆ K
      --------
    → φ ⊢Nf⋆ K
\end{code}

\begin{code}
{-# TERMINATING #-}
readbackNf  : ∀{φ K} → φ ⊢V⋆ K → φ ⊢Nf⋆ K
readbackNeN : ∀{φ K} → φ ⊢Ne⋆ K → φ ⊢NeN⋆ K

readbackNf (Π t vs) = Π (readbackNf (eval t (extEnv vs)))
readbackNf (A ⇒ B)  = readbackNf A ⇒ readbackNf B
readbackNf (ƛ t vs) = ƛ (readbackNf (eval t (extEnv vs)))
readbackNf (μ t vs) = μ (readbackNf (eval t (extEnv vs)))
readbackNf (ne n)   = ne (readbackNeN n)

readbackNeN (` x)    = ` x
readbackNeN (n · n') = readbackNeN n · readbackNf n'
\end{code}
