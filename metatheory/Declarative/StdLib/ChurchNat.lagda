\begin{code}
module Declarative.StdLib.ChurchNat where
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
N = Π "α" (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)

-- /\(r :: *) -> \(z : r) (f : r -> r) -> z
Zero : ∅ ⊢ N
Zero = Λ "α" (ƛ "z" (ƛ "f" (` (S Z))))

-- \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
Succ : ∅ ⊢ N ⇒ N
Succ = ƛ "n" (Λ "α" (ƛ "z" (ƛ "f" (` Z · ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (` Z))))))

Iter : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π "α" (` Z ⇒ (` Z ⇒ ` Z) ⇒ N ⇒ (` Z))
Iter = Λ "α" (ƛ "x" (ƛ "y" (ƛ "z" ((` Z) ·⋆ (` Z) · (` (S (S Z))) · (` (S Z))))))

open import Builtin.Constant.Type
open import Data.Integer
open import Data.Nat
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

{-
con0 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con integer
con0 = con (integer 8 (ℤ.pos 0) _) -- (-≤+ ,, (+≤+ (s≤s z≤n))))

con1 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con integer
con1 = con (integer 8 (ℤ.pos 1) _) -- (-≤+ ,, (+≤+ (s≤s (s≤s z≤n)))))

inc : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π (con integer (` Z) ⇒ con integer (` Z))
inc = Λ (ƛ (builtin addInteger (λ { Z → ` Z ; (S ())}) ((builtin resizeInteger (λ { Z → ` Z ; (S Z) → size⋆ 8 ; (S (S ()))}) (builtin sizeOfInteger (λ { Z → ` Z ; (S ())}) (` Z ,, tt) ,, (con1 ,, tt))) ,, (` Z) ,, tt)))


Nat2Int : ∅ ⊢ N ⇒ con integer (size⋆ 8)
Nat2Int = ƛ (Iter
  ·⋆ con integer (size⋆ 8)
  ·  con0
  ·  (inc ·⋆ size⋆ 8)
  · ` Z)
-}
\end{code}
