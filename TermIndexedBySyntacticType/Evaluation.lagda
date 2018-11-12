\begin{code}
module TermIndexedBySyntacticType.Evaluation where
\end{code}

## Imports

\begin{code}
open import Type
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Term.Reduction
\end{code}

## Evaluation

Transitive closure of reduction
\begin{code}
data _—↠_ {J Γ}{A : ∥ Γ ∥ ⊢⋆ J} (L : Γ ⊢ A) : (Γ ⊢ A) → Set where
  done : L —↠ L
  continue : ∀ {M N} → L —→ M → M —↠ N → L —↠ N  
\end{code}

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

  error :  ∀ {J}{A : ∅ ⊢⋆ J} {L : ∅ ⊢ A} → Steps L

\end{code}
The evaluator takes gas and a term and returns the corresponding steps.
\begin{code}
eval : ∀ {A : ∅ ⊢⋆ *}
  → Gas
  → (M : ∅ ⊢ A)
    -----------
  → Steps M
eval (gas zero) M = steps done out-of-gas
eval (gas (suc n)) M with progress M
...                  | error = error
eval (gas (suc n)) M | step {N} p  with eval (gas n) N
...                               | error = error
eval (gas (suc n)) M | step {N} p | steps ps q = steps (continue p ps) q
eval (gas (suc n)) M | done vM = steps done (done _ vM)
\end{code}
