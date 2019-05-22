\begin{code}
module Algorithmic.Evaluation where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic
open import Algorithmic.Reduction
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
data Finished {Φ Γ}{A : Φ ⊢Nf⋆ *} :  (N : Γ ⊢ A) →  Set where

   done : ∀ N → 
       Value N
       ----------
     → Finished N

   out-of-gas : ∀{N} → 
       ----------
       Finished N

   error : {L : Γ ⊢ A} → Error L → Finished L

\end{code}
Given a term `L` of type `A`, the evaluator will, for some `N`, return
a reduction sequence from `L` to `N` and an indication of whether
reduction finished.
\begin{code}
data Steps : ∀ {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set where

  steps : {A : ∅ ⊢Nf⋆ *} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L


\end{code}

\begin{code}
evalStep : ∀{A : ∅ ⊢Nf⋆ *} → Gas → {t t' : ∅ ⊢ A} → t —→ t' →
  Steps t' → Steps t
evalStep g p (steps ps q) = steps (trans—↠ p ps) q
\end{code}

The evaluator takes gas and a term and returns the corresponding steps.
\begin{code}
eval : ∀ {A : ∅ ⊢Nf⋆ *} → Gas → (M : ∅ ⊢ A) → Steps M
evalNext : ∀{A : ∅ ⊢Nf⋆ *} → Gas → {t : ∅ ⊢ A} → Progress t → Steps t

eval (gas zero) M = steps refl—↠ out-of-gas
eval (gas (suc n)) M = evalNext (gas n) (progress M)

evalNext g (step p)  = evalStep g p (eval g _)
evalNext g (done VM) = steps refl—↠ (done _ VM)
evalNext g (error e) = steps refl—↠ (error e)
\end{code}
