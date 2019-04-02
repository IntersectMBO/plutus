\begin{code}
module Declarative.StdLib.ChurchNat where
\end{code}

\begin{code}
open import Type
open import Declarative.Term
open import Builtin
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆

open import Data.Unit
\end{code}

\begin{code}
-- all (r :: *). r -> (r -> r) -> r
N : ∀{Γ} → Γ ⊢⋆ *
N = Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)

-- /\(r :: *) -> \(z : r) (f : r -> r) -> z
Zero : ∅ ⊢ N
Zero = Λ (ƛ (ƛ (` (S Z))))

-- \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
Succ : ∅ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (` Z))))))

Iter : ∀{Γ} → Γ ⊢ Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ N ⇒ (` Z))
Iter = Λ (ƛ (ƛ (ƛ ((` Z) ·⋆ (` Z) · (` (S (S Z))) · (` (S Z))))))

open import Builtin.Constant.Type
open import Data.Integer
open import Data.Nat
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

con0 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con0 = con (integer 8 (ℤ.pos 0) (-≤+ ,, (+≤+ (s≤s z≤n))))

con1 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con1 = con (integer 8 (ℤ.pos 1) (-≤+ ,, (+≤+ (s≤s (s≤s z≤n)))))

inc : ∀{Γ} → Γ ⊢ Π (con integer (` Z) ⇒ con integer (` Z))
inc = Λ (ƛ (builtin addInteger (λ { Z → ` Z ; (S ())}) ((builtin resizeInteger (λ { Z → ` Z ; (S Z) → size⋆ 8 ; (S (S ()))}) (builtin sizeOfInteger (λ { Z → ` Z ; (S ())}) (` Z ,, tt) ,, (con1 ,, tt))) ,, (` Z) ,, tt)))


Nat2Int : ∅ ⊢ N ⇒ con integer (size⋆ 8)
Nat2Int = ƛ (Iter
  ·⋆ con integer (size⋆ 8)
  ·  con0
  ·  (inc ·⋆ size⋆ 8)
  · ` Z)
\end{code}
