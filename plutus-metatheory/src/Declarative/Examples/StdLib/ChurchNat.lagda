\begin{code}
module Declarative.Examples.StdLib.ChurchNat where
\end{code}

\begin{code}
open import Data.Integer using (ℤ)

open import Utils using (Kind;*;AtomicTyCon)
open AtomicTyCon
open import Type using (Ctx⋆;_⊢⋆_;Z)
open _⊢⋆_
open import Declarative using (Ctx;_⊢_;_∋_)
open Ctx
open _⊢_
open _∋_
open import Builtin using (addInteger)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con using (TermCon)
open TermCon
open import Builtin.Constant.Type using (TyCon)
open TyCon
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

con0 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (atomic integer)
con0 = con (integer (ℤ.pos 0))

con1 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (atomic integer)
con1 = con (integer (ℤ.pos 1))

inc : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (atomic integer) ⇒ con (atomic integer)
inc = ƛ (builtin addInteger · con1  · ` Z)

Nat2Int : ∅ ⊢ N ⇒ con (atomic integer)
Nat2Int = ƛ (Iter
  ·⋆ con (atomic integer)
  ·  con0
  ·  inc
  ·  ` Z)
\end{code}
