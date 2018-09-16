\begin{code}
module Evaluation where
\end{code}

## Imports

\begin{code}
open import Type
open import Term
open import Term.Reduction
\end{code}

## Evaluation

As previously, gas is specified by a natural number.
\begin{code}
open import Data.Nat
data Gas : Set where
  gas : ℕ → Gas
\end{code}
When our evaluator returns a term `N`, it will either give evidence that
`N` is a value or indicate that it ran out of gas.
\begin{code}
data Finished {Γ J}{A : ∥ Γ ∥ ⊢⋆ J} :  (N : Γ ⊢ A) →  Set where

   done : ∀ N → 
       Value N
       ----------
     → Finished N

   out-of-gas : ∀{N} → 
       ----------
       Finished N
\end{code}
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished.
\begin{code}
data Steps : ∀ {J}{A : ∅ ⊢⋆ J} → ∅ ⊢ A → Set where

  steps : ∀ {J}{A : ∅ ⊢⋆ J} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

  unhandled-conversion :  ∀ {J}{A : ∅ ⊢⋆ J} {L : ∅ ⊢ A} → Steps L

\end{code}
The evaluator takes gas and a term and returns the corresponding steps.
\begin{code}
{-
eval : ∀ {A : ∅ ⊢⋆ *}
  → Gas
  → (M : ∅ ⊢ A)
    -----------
  → Steps M
eval (gas zero) M = steps done out-of-gas
eval (gas (suc n)) M with progress M
...                  | unhandled-conversion = unhandled-conversion
eval (gas (suc n)) M | step {N} p  with eval (gas n) N
...                               | unhandled-conversion = unhandled-conversion
eval (gas (suc n)) M | step {N} p | steps ps q = steps (continue p ps) q
eval (gas (suc n)) M | done vM = steps done (done _ vM)
-}
\end{code}
