\begin{code}
module Declarative.Examples.StdLib.ChurchNat where
\end{code}

\begin{code}
open import Type
open import Declarative
open import Builtin
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con

open import Data.Unit
\end{code}

\begin{code}
-- all (r :: *). r -> (r -> r) -> r
N : ∀{Φ} → Φ ⊢⋆ *
N = Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)

-- /\(r :: *) -> \(z : r) (f : r -> r) -> z
Zero : ∅ ⊢ N
Zero = Λ (ƛ (ƛ (` (S Z))))

-- \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
Succ : ∅ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (` Z))))))

Iter : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ N ⇒ (` Z))
Iter = Λ (ƛ (ƛ (ƛ ((` Z) ·⋆ (` Z) · (` (S (S Z))) · (` (S Z))))))

open import Builtin.Constant.Type
open import Data.Integer
open import Data.Nat
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

con0 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con integer
con0 = con (integer (ℤ.pos 0))

con1 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con integer
con1 = con (integer (ℤ.pos 1))

inc : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con integer ⇒ con integer
inc = ƛ (builtin
  addInteger
  (λ())
  (con1 ∷ (` Z ∷ [])))

Nat2Int : ∅ ⊢ N ⇒ con integer
Nat2Int = ƛ (Iter
  ·⋆ con integer
  ·  con0
  ·  inc
  ·  ` Z)

\end{code}
